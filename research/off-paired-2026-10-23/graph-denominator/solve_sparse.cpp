// Bounded, single-threaded sparse Gaussian elimination over a prime field.
// Binary input: uint32 rows, cols, p, nnz; cols+1 sparse columns,
// each uint32 size followed by (uint32 row,uint32 coefficient) pairs.
// The last column is the right hand side. All words use host little endian.
// Compile: g++ -O3 -std=c++17 -DNDEBUG solve_sparse.cpp -o solve_sparse
// Usage: solve_sparse INPUT [OUTPUT.json] [MAX_SECONDS=1800] [MAX_RSS_MB=5500]
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <queue>
#include <stdexcept>
#include <string>
#include <sys/resource.h>
#include <utility>
#include <vector>

using U=uint32_t; using W=uint64_t;
using Entry=std::pair<U,U>; using Row=std::vector<Entry>;
using Clock=std::chrono::steady_clock;
struct Pivot { U col,rhs; Row entries; };
struct HeapEntry { U degree,id; bool operator>(const HeapEntry &x) const {
    return degree>x.degree || (degree==x.degree && id>x.id); } };
using Heap=std::priority_queue<HeapEntry,std::vector<HeapEntry>,std::greater<HeapEntry>>;

static U read_u32(std::ifstream &in) {
    U x; in.read(reinterpret_cast<char*>(&x),4);
    if(!in) throw std::runtime_error("truncated binary input"); return x;
}
static U inverse(U a,U p) {
    U e=p-2,z=1; while(e) { if(e&1) z=W(z)*a%p; a=W(a)*a%p; e>>=1; } return z;
}
static W rss_mb() { struct rusage r{}; getrusage(RUSAGE_SELF,&r); return W(r.ru_maxrss)/1024; }

class Solver {
public:
    U m,n,p; W initial_nnz=0,active_nnz=0,history_nnz=0;
    std::vector<Row> rows;
    std::vector<U> rhs,cd,stamp;
    std::vector<uint8_t> live_row,live_col,dirty_flag;
    std::vector<std::vector<U>> incidence;
    std::vector<U> dirty;
    std::vector<Pivot> pivots;
    Heap rh,ch;
    bool contradiction=false,complete=false;
    U first_contradiction_rank=0;
    W merged_entries=0;
    Clock::time_point start=Clock::now(),last_print=start;
    std::string reason;

    explicit Solver(const std::string &path) {
        std::ifstream in(path,std::ios::binary); if(!in) throw std::runtime_error("cannot open input");
        m=read_u32(in); n=read_u32(in); p=read_u32(in); initial_nnz=read_u32(in);
        if(p<5 || m>1000000 || n>1000000) throw std::runtime_error("invalid header");
        rows.resize(m); rhs.assign(m,0); cd.assign(n,0); stamp.assign(m,0);
        incidence.resize(n); live_row.assign(m,1); live_col.assign(n,1); dirty_flag.assign(n,0);
        for(U c=0;c<=n;c++) {
            U sz=read_u32(in);
            for(U j=0;j<sz;j++) {
                U r=read_u32(in),v=read_u32(in)%p;
                if(r>=m) throw std::runtime_error("row out of range");
                if(!v) continue;
                if(c==n) rhs[r]=(rhs[r]+W(v))%p;
                else rows[r].emplace_back(c,v);
            }
        }
        for(U r=0;r<m;r++) {
            Row clean; clean.reserve(rows[r].size());
            // Input columns are increasing; combine any duplicate entries defensively.
            for(auto [c,v]:rows[r]) {
                if(!clean.empty() && clean.back().first==c) {
                    clean.back().second=(clean.back().second+W(v))%p;
                    if(!clean.back().second) clean.pop_back();
                } else clean.emplace_back(c,v);
            }
            rows[r].swap(clean);
            if(rows[r].empty()) { live_row[r]=0; if(rhs[r]) note_contradiction(); continue; }
            rh.push({U(rows[r].size()),r});
            active_nnz+=rows[r].size();
            for(auto [c,v]:rows[r]) { ++cd[c]; incidence[c].push_back(r); }
        }
        history_nnz=active_nnz;
        for(U c=0;c<n;c++) if(cd[c]) ch.push({cd[c],c});
    }
    double seconds() const { return std::chrono::duration<double>(Clock::now()-start).count(); }
    void note_contradiction(U rank_at_detection=std::numeric_limits<U>::max()) {
        if(rank_at_detection==std::numeric_limits<U>::max()) rank_at_detection=pivots.size();
        if(!contradiction) { contradiction=true; first_contradiction_rank=rank_at_detection;
            std::cerr<<"contradiction after "<<rank_at_detection<<" pivots at "<<seconds()<<"s\n"; }
    }
    U value(U r,U c) const {
        const Row &v=rows[r]; auto it=std::lower_bound(v.begin(),v.end(),Entry(c,0));
        return it!=v.end() && it->first==c ? it->second : 0;
    }
    void changed(U c) { if(!dirty_flag[c]) { dirty_flag[c]=1; dirty.push_back(c); } }
    void refresh_heaps() {
        if(rh.size()>W(m)*6+10000) {
            Heap nr; for(U r=0;r<m;r++) if(live_row[r]) nr.push({U(rows[r].size()),r}); rh.swap(nr);
        }
        if(ch.size()>W(n)*6+10000) {
            Heap nc; for(U c=0;c<n;c++) if(live_col[c] && cd[c]) nc.push({cd[c],c}); ch.swap(nc);
        }
    }
    void compact_column(U c) {
        auto &v=incidence[c];
        // A temporary stamp removes duplicate historical memberships.
        std::vector<U> w; w.reserve(cd[c]);
        for(U r:v) if(live_row[r] && value(r,c)) w.push_back(r);
        std::sort(w.begin(),w.end()); w.erase(std::unique(w.begin(),w.end()),w.end());
        history_nnz-=v.size(); history_nnz+=w.size(); v.swap(w);
        if(v.size()!=cd[c]) throw std::runtime_error("column degree invariant failed");
    }
    std::pair<U,U> choose() {
        W best=std::numeric_limits<W>::max(),best_sum=best; U br=m,bc=n;
        auto consider=[&](U r,U c) {
            W a=rows[r].size(),b=cd[c],score=(a-1)*(b-1),sum=a+b;
            if(score<best || (score==best && (sum<best_sum || (sum==best_sum && std::make_pair(r,c)<std::make_pair(br,bc))))) {
                best=score;best_sum=sum;br=r;bc=c;
            }
        };
        std::vector<HeapEntry> saved;
        W work=0;
        while(saved.size()<32 && !rh.empty()) {
            auto e=rh.top();rh.pop();
            if(!live_row[e.id] || e.degree!=rows[e.id].size()) continue;
            saved.push_back(e);
            for(auto [c,v]:rows[e.id]) consider(e.id,c);
            work+=rows[e.id].size();
            if(best==0 || work>10000) break;
        }
        for(auto e:saved) rh.push(e);
        if(best==0) return {br,bc};
        saved.clear();work=0;
        while(saved.size()<8 && !ch.empty()) {
            auto e=ch.top();ch.pop();
            if(!live_col[e.id] || !cd[e.id] || e.degree!=cd[e.id]) continue;
            saved.push_back(e);
            if(incidence[e.id].size()>W(cd[e.id])*3+512) compact_column(e.id);
            U hits=0;
            for(U r:incidence[e.id]) if(live_row[r] && value(r,e.id)) {
                consider(r,e.id); ++hits; if(++work>10000 || hits>=1024) break;
            }
            if(best==0 || work>10000) break;
        }
        for(auto e:saved) ch.push(e);
        return {br,bc};
    }
    void eliminate(U pr,U pc) {
        U z=inverse(value(pr,pc),p);
        Pivot pv{pc,U(W(rhs[pr])*z%p),std::move(rows[pr])};
        for(auto &e:pv.entries) e.second=W(e.second)*z%p;
        live_row[pr]=0; active_nnz-=pv.entries.size();
        for(auto [c,v]:pv.entries) { --cd[c]; changed(c); }
        live_col[pc]=0;
        U token=pivots.size()+1;
        // No new pc membership is introduced during this operation.
        for(U r:incidence[pc]) {
            if(!live_row[r] || stamp[r]==token) continue;
            stamp[r]=token; U a=value(r,pc); if(!a) continue;
            const Row &old=rows[r]; Row next;
            next.reserve(old.size()+pv.entries.size());
            size_t i=0,j=0;
            while(i<old.size() || j<pv.entries.size()) {
                if(j==pv.entries.size() || (i<old.size() && old[i].first<pv.entries[j].first)) {
                    next.push_back(old[i++]);
                } else if(i==old.size() || pv.entries[j].first<old[i].first) {
                    auto [c,v]=pv.entries[j++]; U t=W(a)*v%p;
                    if(t) { next.emplace_back(c,p-t); ++cd[c]; changed(c); incidence[c].push_back(r); ++history_nnz; }
                } else {
                    U c=old[i].first,t=W(a)*pv.entries[j].second%p,v=old[i].second;
                    U out=v>=t?v-t:v+(p-t); ++i;++j;
                    if(out) next.emplace_back(c,out);
                    else { --cd[c]; changed(c); }
                }
            }
            merged_entries+=old.size()+pv.entries.size();
            active_nnz-=old.size(); active_nnz+=next.size(); rows[r].swap(next);
            U t=W(a)*pv.rhs%p; rhs[r]=rhs[r]>=t?rhs[r]-t:rhs[r]+(p-t);
            if(rows[r].empty()) { live_row[r]=0; if(rhs[r]) note_contradiction(pivots.size()+1); }
            else rh.push({U(rows[r].size()),r});
        }
        if(cd[pc]) throw std::runtime_error("pivot column did not clear");
        history_nnz-=incidence[pc].size(); std::vector<U>().swap(incidence[pc]);
        pivots.push_back(std::move(pv));
        for(U c:dirty) {
            dirty_flag[c]=0;
            if(live_col[c] && cd[c]) ch.push({cd[c],c});
        }
        dirty.clear();
    }
    void progress(bool force=false) {
        auto now=Clock::now();
        if(force || std::chrono::duration<double>(now-last_print).count()>=15) {
            std::cerr<<std::fixed<<std::setprecision(1)<<"seconds="<<seconds()<<" rank="<<pivots.size()
              <<" active_nnz="<<active_nnz<<" incidence="<<history_nnz<<" rss_mb="<<rss_mb()
              <<" merged="<<merged_entries<<" contradiction="<<(contradiction?"yes":"no")<<"\n";
            last_print=now;
        }
    }
    void run(double max_seconds,W max_rss) {
        progress(true);
        while(true) {
            if(seconds()>max_seconds) { reason="time_limit";break; }
            if(rss_mb()>max_rss) { reason="memory_limit";break; }
            auto [r,c]=choose();
            if(r==m) { complete=true;reason=contradiction?"inconsistent_mod_p":"consistent_mod_p";break; }
            eliminate(r,c); progress();
            if(pivots.size()%64==0) {
                refresh_heaps();
                if(history_nnz>active_nnz*4+W(n)*1024) {
                    for(U k=0;k<n;k++) if(live_col[k] && incidence[k].size()>W(cd[k])*3+512) compact_column(k);
                }
            }
        }
        progress(true);
    }
    void write(const std::string &out) {
        std::ofstream f(out); if(!f) throw std::runtime_error("cannot open output");
        f<<"{\n  \"prime\": "<<p<<",\n  \"rows\": "<<m<<",\n  \"columns\": "<<n
         <<",\n  \"status\": \""<<reason<<"\",\n  \"complete_rank\": "<<(complete?"true":"false")
         <<",\n  \"rank\": "<<pivots.size()<<",\n  \"contradiction\": "<<(contradiction?"true":"false")
         <<",\n  \"first_contradiction_rank\": "<<first_contradiction_rank
         <<",\n  \"seconds\": "<<seconds()<<",\n  \"peak_rss_mb\": "<<rss_mb()
         <<",\n  \"active_nnz\": "<<active_nnz<<",\n  \"merged_entries\": "<<merged_entries;
        if(complete && !contradiction) {
            std::vector<U> solution(n,0);
            for(auto it=pivots.rbegin();it!=pivots.rend();++it) {
                U v=it->rhs;
                for(auto [c,a]:it->entries) if(c!=it->col) { U t=W(a)*solution[c]%p;v=v>=t?v-t:v+(p-t); }
                solution[it->col]=v;
            }
            f<<",\n  \"solution\": ["; for(U c=0;c<n;c++) {if(c)f<<",";f<<solution[c];} f<<"]";
        }
        f<<"\n}\n";
    }
};

int main(int argc,char **argv) {
    if(argc<2) { std::cerr<<"usage: solve_sparse INPUT [OUTPUT.json] [MAX_SECONDS] [MAX_RSS_MB]\n";return 2; }
    try {
        std::string out=argc>2?argv[2]:std::string(argv[1])+".result.json";
        Solver s(argv[1]); s.run(argc>3?std::stod(argv[3]):1800,argc>4?std::stoull(argv[4]):5500);
        s.write(out); std::cout<<out<<"\n";return s.complete?0:3;
    } catch(const std::exception &e) { std::cerr<<"error: "<<e.what()<<"\n";return 2; }
}
