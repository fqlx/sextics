#!/usr/bin/env python3
"""Fill-free singleton/two-variable elimination, a preliminary modular screen."""
import collections,json,struct,time,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
p=int(sys.argv[1]) if len(sys.argv)>1 else 1000003
started=time.time()
with (ROOT/f'system-{p}.bin').open('rb') as f:
    nr,nc,prime,nnz=struct.unpack('<4I',f.read(16));assert p==prime
    rows=[{} for _ in range(nr)];rhs=[0]*nr;inc=[set() for _ in range(nc)]
    for j in range(nc+1):
        n=struct.unpack('<I',f.read(4))[0]
        for r,v in struct.iter_unpack('<II',f.read(8*n)):
            if j==nc:rhs[r]=v
            else:rows[r][j]=v;inc[j].add(r)

pending=collections.deque(r for r in range(nr) if len(rows[r])<=2)
eliminated=set();rank=0;contradiction=None
while pending:
    r=pending.popleft();row=rows[r]
    if not row:
        if rhs[r]:contradiction=r;break
        continue
    if len(row)>2:continue
    pivot=min(row,key=lambda j:len(inc[j]))
    factor=pow(row[pivot],-1,p)
    source={j:v*factor%p for j,v in row.items() if j!=pivot}
    source_rhs=rhs[r]*factor%p
    affected=list(inc[pivot])
    for s in affected:
        target=rows[s]
        a=target.pop(pivot);inc[pivot].discard(s)
        rhs[s]=(rhs[s]-a*source_rhs)%p
        for j,v in source.items():
            new=(target.get(j,0)-a*v)%p
            if new:target[j]=new;inc[j].add(s)
            else:target.pop(j,None);inc[j].discard(s)
        if len(target)<=2:pending.append(s)
    rank+=1;eliminated.add(pivot)
    if rank%500==0:print(json.dumps({'rank':rank,'seconds':round(time.time()-started,2)}),flush=True)

report={'prime':p,'stage':'singleton_and_two_variable_peeling',
        'pivots':rank,'remaining_variables':nc-rank,
        'remaining_equations':sum(bool(row) for row in rows),
        'remaining_nonzeros':sum(map(len,rows)),
        'modular_status':'inconsistent' if contradiction is not None else 'undetermined',
        'contradiction_row':contradiction,'seconds':time.time()-started}
(ROOT/f'peel-{p}.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
