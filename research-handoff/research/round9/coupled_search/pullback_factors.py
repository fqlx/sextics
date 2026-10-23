#!/usr/bin/env python3
"""Native exact pullbacks of all three GM denominator factors."""
import json,pickle,time,sympy as s
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq
P=Path(__file__).resolve().parent
d=pickle.load(open('/workspace/research/round8/coupled_source/jacobian_native.pickle','rb'))
g=pickle.load(open('/workspace/research/round9/cyclic_full/actual_fast.pickle','rb'));L,r,x=g['symbols'][3:]
ctx=fmpq_mpoly_ctx.get(('a','b','v'))
pol={k:ctx.from_dict({e:fmpq(c) for e,c in z.items()}) for k,z in d.items()}
A,B,H,J=[pol[k] for k in ('A','B','H','J')]
D=s.denom(g['connection']['r'][0,0]);D1=27*L**2+4*r**3*x
D2=-50824368*L**2-4321800*L*r*x+15625*L*x**2+1102500*L*x+12965400*L-7529536*r**3*x+30625*r**2*x**2+5762400*r**2*x-15625*r*x**2-918750*r*x-15625*x-826875
out={};summary={};start=time.time()
for name,f in [('D',D),('D1',D1),('D2',D2)]:
    terms=s.Poly(f,L,r,x).as_dict()
    ua=max(2*i+j+k for i,j,k in terms);ub=max(j-3*k for i,j,k in terms)
    n=ctx.constant(0)
    for (i,j,k),c in terms.items():
        n+=fmpq(str(c))*fmpq(3)**(k-i)*H**i*J**j*B**(ub+3*k-j)*A**(ua-2*i-j-k)
    print(name,'constructed',len(n.to_dict()),'seconds',time.time()-start,flush=True)
    scalar,factors=n.factor();prod=ctx.constant(scalar)
    for z,e in factors:prod*=z**e
    assert prod==n
    out[name]={'numerator':{e:str(c) for e,c in n.to_dict().items()},'denominatorA':ua,'denominatorB':ub,'constant':str(scalar),'factors':[({'coefficients':{e:str(c) for e,c in z.to_dict().items()},'exponent':int(m)}) for z,m in factors]}
    summary[name]={'clearA':ua,'clearB':ub,'terms':len(n.to_dict()),'constant':str(scalar),'factors':[{'exponent':int(m),'terms':len(z.to_dict()),'degrees':[int(t) for t in z.degrees()],'polynomial':str(z) if len(z.to_dict())<15 else None} for z,m in factors]}
    print(name,summary[name],flush=True)
pickle.dump(out,open(P/'gm_pullback_factors_QQ.pickle','wb'));(P/'gm_pullback_factors_QQ.json').write_text(json.dumps(summary,indent=2))
