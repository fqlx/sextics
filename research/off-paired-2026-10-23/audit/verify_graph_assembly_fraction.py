#!/usr/bin/env python3
"""Independent target, six-support and source-addition matrix audit.

Uses exact Fraction polynomial identities and samples the saved modular
columns. Does not import or rerun the large constructor or linear solver.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import struct
from verify_connection_fraction import Ring,record


def mons(d,n=6):
    if n==1:yield (d,);return
    for i in range(d+1):
        for rest in mons(d-i,n-1):yield (i,)+rest


def main():
    root=Path('/workspace/off-paired-research-new/graph-assembly')
    meta=root/'assembly-XY-1000003.json'
    data=json.loads(meta.read_text())
    r=Ring(['X0','X1','X2','Y0','Y1','Y2'])
    _,target=record(Path('/workspace/off-paired-sextics/data/off-paired/instance.rec'))
    F,A=r.poly(target['F']),r.poly(target['A']);assert target['q']=='1'
    decode=lambda items:{tuple(e):Q(c) for e,c in items}
    assert decode(data['F'])==F and decode(data['A'])==A
    specs=[('X',0),('X',1),('X',2),('Y',0),('Y',1),('Y',2)]
    assert [tuple(z) for z in data['support_specs']]==specs
    HX=r.poly('X0**6+X1**6+X2**6');FY=r.poly('Y0**6+Y1**6+Y2**6')
    ds=[]
    for block,held in specs:
        chosen=[i for i in range(3) if i!=held]
        powers=[r.power(r.var(block+str(i)),6) for i in chosen]
        T=r.add(*powers);K=r.mul(*powers)
        D=r.add(r.mul(FY,r.power(T,2)),r.scale(r.mul(HX,K),16))
        assert D==decode(data['denominators'][len(ds)])
        assert all(sum(e)==18 for e in D)
        ds.append(D)
    # Universal same-kappa graph factorization; no X/Y block interchange.
    u=Ring(['H','C','M','T','K']);up=u.poly
    D54=up('16*K*T**4*M**3-H**2*C*(T**2-16*K)**3')
    D18=up('C*T**2+16*H*K')
    Q36=up('16*K*C**2*T**2+48*K*H*C*T**2-256*K**2*H*C+H**2*T**4')
    lift=up('16*K*T**4*(H+C+M)*(M**2-M*(H+C)+(H+C)**2)')
    assert not u.add(D54,u.mul(D18,Q36),u.scale(lift,-1))

    # Absolute complex coprimality for every denominator by a nonzero
    # resultant specialization, leaving one chosen Y coordinate free.
    single=Ring(['y']);gcd_witnesses=[]
    for (block,held),D in zip(specs,ds):
        varying=0 if block=='X' else next(i for i in range(3) if i!=held)
        vals={name:single.const(1) for name in r.names[:3]}
        vals.update({name:(single.var('y') if i==varying else {}) for i,name in enumerate(r.names[3:])})
        ff=r.subst(F,vals,single);dd=r.subst(D,vals,single)
        assert ff==single.poly('y**6+3')
        if block=='X':
            assert dd==single.poly('4*y**6+48')
            assert single.add(dd,single.scale(ff,-4))==single.const(36)
            gcd_witnesses.append({'support':[block,held],'free_variable':'Y'+str(varying),'D_mod_F':'36','resultant':'36^6'})
        else:
            assert dd==single.poly('y**18')
            # y^18+27=(y^6+3)(y^12-3y^6+9).
            assert not single.add(dd,single.const(27),single.scale(single.mul(ff,single.poly('y**12-3*y**6+9')),-1))
            gcd_witnesses.append({'support':[block,held],'free_variable':'Y'+str(varying),'D_mod_F':'-27','resultant':'(-27)^6'})
    weights=[(0,0),(2,0),(0,1),(1,0),(3,0),(3,5)]
    char=lambda e:tuple(sum(e[i]*weights[i][j] for i in range(6))%6 for j in range(2))
    sources=[e for e in mons(6) if char(e)==(3,0)]
    assert len(sources)==24 and sources==[tuple(e) for e in data['source_exponents']]
    n_specs=[]
    for i in range(6):
        want=tuple(((3,0)[j]+weights[i][j])%6 for j in range(2))
        n_specs += [(i,e) for e in mons(19) if e[3]<6 and (i!=3 or e[3]==0) and char(e)==want]
    expected=[]
    for block,held in specs:
        expected += [['N',block,held,i,list(e)] for i,e in n_specs]
        expected += [['source',block,held,list(e)] for e in sources]
    assert expected==data['names'] and len(n_specs)==5291
    assert all(char(e)==(0,0) for D in ds for e in D)
    rows=[(support,tuple(value) if support<6 else value) for support,value in data['row_exponents']]
    assert len(rows)==data['rows'] and len(set(rows))==len(rows)
    assert all(sum(e)==42 and e[3]<12 and char(e)==(3,0) for s,e in rows if s<6)
    assert sorted(e for s,e in rows if s==6)==list(range(24))
    FF=r.power(F,2);leading=(0,0,0,12,0,0)
    assert FF[leading]==1
    def rem(poly):
        poly=dict(poly)
        while any(e[3]>=12 for e in poly):
            e=max((e for e in poly if e[3]>=12),key=lambda e:(e[3],e))
            shift=tuple(e[i]-leading[i] for i in range(6));co=poly[e]
            poly=r.add(poly,r.scale(r.mul({shift:Q(1)},FF),-co))
        return poly
    def L(D,i,N):
        return r.add(r.scale(r.mul(D,r.mul(N,r.diff(F,r.names[i]))),-1),r.mul(F,
           r.add(r.mul(D,r.diff(N,r.names[i])),r.scale(r.mul(N,r.diff(D,r.names[i])),-1))))
    prime=data['prime']
    def cv(poly):return {e:co.numerator*pow(co.denominator,-1,prime)%prime for e,co in poly.items() if co.numerator%prime}
    block_size=len(n_specs)+len(sources)
    source_A=sources.index(next(iter(A)))
    source_high=max(range(24),key=lambda i:(sources[i][3],sources[i]))
    n_y0=next(i for i,(comp,e) in enumerate(n_specs) if comp==3)
    n_high=max(range(len(n_specs)),key=lambda i:(n_specs[i][1][3],n_specs[i][1]))
    sample_indices={j*block_size+i for j in range(6) for i in [n_y0,n_high,len(n_specs)+source_A,len(n_specs)+source_high]}
    wanted=set(sample_indices)|{len(expected)}
    selected={};all_source_cols=0;total_nnz=0
    binary=root/'assembly-XY-1000003.bin'
    with binary.open('rb') as f:
        header=struct.unpack('<4I',f.read(16))
        assert header[:3]==(len(rows),len(expected),prime)
        for i in range(len(expected)+1):
            nnz,=struct.unpack('<I',f.read(4));total_nnz+=nnz
            is_source=i<len(expected) and expected[i][0]=='source'
            if i in wanted or is_source:
                values={}
                for row,co in struct.iter_unpack('<II',f.read(8*nnz)):
                    assert row<len(rows) and 0<co<prime and row not in values
                    values[row]=co
                if i in wanted:selected[i]=values
                if is_source:
                    name=expected[i];support=specs.index((name[1],name[2]));src=sources.index(tuple(name[3]))
                    additions=[(rows[row],co) for row,co in values.items() if rows[row][0]==6]
                    assert additions==[((6,src),1)]
                    assert all(rows[row][0] in [support,6] for row in values)
                    all_source_cols+=1
            else:f.seek(8*nnz,1)
        assert not f.read(1) and total_nnz==header[3]
    assert all_source_cols==144
    for idx in sorted(sample_indices):
        name=expected[idx];support=specs.index((name[1],name[2]));D=ds[support]
        if name[0]=='N':
            poly=cv(rem(L(D,name[3],{tuple(name[4]):Q(1)})))
            wanted_col={(support,e):co for e,co in poly.items()}
        else:
            ex=tuple(name[3]);poly=cv(rem(r.mul({ex:Q(1)},r.power(D,2))))
            wanted_col={(support,e):co for e,co in poly.items()}
            wanted_col[(6,sources.index(ex))]=1
        actual_col={rows[row]:co for row,co in selected[idx].items()}
        assert actual_col==wanted_col,idx
    assert {rows[row]:co for row,co in selected[len(expected)].items()}=={(6,source_A):1}
    # Exact rational-current addition after common-denominator clearing:
    # L_(D1D2)(N1D2)=D2^2 L_D1(N1), independent of source relations.
    N=r.poly('X0**3*X1**4*X2**2*Y0**3*Y1**5*Y2**2')
    assert sum(next(iter(N)))==19
    for left,right in [(0,1),(0,3),(3,5)]:
        combined=r.mul(ds[left],ds[right])
        assert not r.add(L(combined,2,r.mul(N,ds[right])),r.scale(r.mul(r.power(ds[right],2),L(ds[left],2,N)),-1))
    result={'status':'passed','supports':specs,'rows':len(rows),'columns':len(expected),
        'source_dimension':len(sources),'all_144_source_addition_columns_checked':True,
        'sample_columns_exactly_checked':len(sample_indices),'sample_indices':sorted(sample_indices),
        'full_rhs_exactly_checked':True,'target_q':1,
        'same_kappa_X_and_Y_support_factorization':True,
        'complex_coprimality_witnesses':gcd_witnesses,
        'exact_source_assembly_identity':'D=prod Di; N=sum Ni*(D/Di); Q=sum Qi*(D/Di)^2 when sum Ai=A',
        'build_script_sha256':hashlib.sha256((root/'build_assembly.py').read_bytes()).hexdigest(),
        'metadata_sha256':hashlib.sha256(meta.read_bytes()).hexdigest(),
        'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
        'scope':'Exact construction, target, same-kappa graph supports, gauges, source addition and sampled matrix verified. No large solver rerun or characteristic-zero rank claim. A candidate requires exact original identity after reconstruction; no certificate has been found.'}
    Path(__file__).with_name('graph-assembly-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
