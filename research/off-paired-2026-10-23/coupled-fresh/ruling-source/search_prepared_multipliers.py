"""Fast constructive three-box search using cached Taylor responses.

Import the independently audited operator implementation unchanged. A trial
span that gives no candidate is only construction feedback.
"""
import importlib.util,itertools,json,random,time
from pathlib import Path

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('heat',HERE/'search_heat_multiplier.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def spans(mode):
    if mode=='matched_branch':
        common=[f'k**{l}*z**{n}*{g}' for l in range(6) for n in (0,2,4) for g in ('1','R','S','T')]
        return [[f'({g})/Delta' for g in common],
                [f'({g})/Delta' for g in common],
                [f'({g})*Delta' for g in common]]
    if mode=='matched_branch_union':
        common=[f'k**{l}*z**{n}*{g}' for l in range(6) for n in (0,2,4) for g in ('1','R','S','T')]
        simple=[f'k**{l}*z**{n}' for l in range(6) for n in (0,2,4)]
        return [[f'({g})/Delta' for g in common]+simple,
                [f'({g})/Delta' for g in common]+simple,
                [f'({g})*Delta' for g in common]+simple]
    if mode=='finite_characters':
        return [f'k**{l}*z**{n}*Delta**{d}' for l in range(6) for n in (0,2,4) for d in (-1,0,1)]
    if mode=='finite_characters_linear':
        return [f'k**{l}*z**{n}*{g}/Delta' for l in range(6) for n in (0,2,4) for g in ('1','R','S','T')]
    if mode=='characters':
        return [f'k**{l}*z**{n}*Delta**{d}' for l in range(3) for n in range(6) for d in (-1,0,1)]
    if mode=='characters_a':
        return [f'k**{l}*z**{n}*Delta**{d}*A**{a}' for l in range(2) for n in range(6) for d in (-1,0,1) for a in (-1,0,1)]
    if mode=='torus':
        return [f'k**{l}*z**{n}*Delta**{d}*{g}' for l in range(3) for n in range(3) for d in (-1,0,1) for g in ('1','A','B','T')]
    raise ValueError(mode)

def solve(mode):
    names=spans(mode)
    if not isinstance(names[0],list):names=[names,names,names]
    unknowns=sum(map(len,names))
    monoms=[e for e in itertools.product(range(4),repeat=3) if sum(e)<=3]
    testjets=[m.Jet({e:1}) for e in monoms]
    rows=[];points=[];rng=random.Random(571057);start=time.monotonic()
    for j in range(unknowns+12):
        while True:
            pt=tuple(rng.randrange(1,m.P) for _ in range(3))
            try:env,H,op,rhs,op2,op3=m.prepare(*pt);break
            except (ValueError,ZeroDivisionError):pass
        weights=[[f(H*v) for v in testjets] for f in (op,op2,op3)]
        row=[]
        for ww,nn in zip(weights,names):
            jets=[m.evaluate(name,env) for name in nn]
            row += [sum(w*v.c.get(e,0) for w,e in zip(ww,monoms))%m.P for v in jets]
        rows.append(row+[rhs]);points.append(pt)
        if (j+1)%50==0:print(f'{mode}: {j+1}/{unknowns+12} point rows, {time.monotonic()-start:.1f}s',flush=True)
    ok,rank,sol=m.rref_solve(rows,unknowns)
    result={'status':'candidate' if ok else 'no candidate in this constructive span',
       'prime':m.P,'span':mode,'multiplier_count':unknowns,'row_count':len(rows),
       'rank':rank,'basis_per_operator':names,
       'coefficients_mod_p':sol if ok else None,
       'seconds':round(time.monotonic()-start,3),
       'normalization':'w1=Hf1,w2=Hf2,w3=H(c/C)^(-1)f3',
       'scope':'constructive search feedback only; a modular hit requires rational reconstruction and literal source/current verification'}
    (HERE/f'prepared-multiplier-{mode}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='basis_per_operator'},indent=2))
if __name__=='__main__':
    import sys
    solve(sys.argv[1] if len(sys.argv)>1 else 'characters')
