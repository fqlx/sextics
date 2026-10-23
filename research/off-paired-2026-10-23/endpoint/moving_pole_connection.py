import sympy as s,json
from pathlib import Path
p,H,C,r=s.symbols('p H C r');f=(H+C*p)**2-4*p**6;fr=f.subs(p,r);bs=[0,1,3,4]
unknowns=s.symbols('m0:4')+s.symbols('r0:6');R=sum(unknowns[4+i]*p**i for i in range(6))
E=sum(unknowns[i]*p**k*f for i,k in enumerate(bs))+s.diff(R,p)*f-R*s.diff(f,p)/2
matrix,_=s.linear_eq_to_matrix(s.Poly(E,p).all_coeffs(),unknowns)
# The linear Hermite reduction map needs to be solved only on six monomials.
reductions=[]
for n in range(6):
 rhs=s.Matrix([1 if i==n else 0 for i in range(10,-1,-1)])
 vec=[s.factor(a)for a in list(s.linsolve((matrix,rhs),unknowns))[0]]
 assert s.cancel((E-p**n).subs(dict(zip(unknowns,vec))))==0
 reductions.append(vec)
 print('reduced monomial',n,flush=True)
out={'basis':bs,'pole':'r','denominator':'f(r)=(H+C*r)**2-4*r**6','columns':{},'exact_primitives':{}}
for v in [H,C,r]:
 fv=s.diff(f,v)if v!=r else s.diff(f,p)
 fvr=fv.subs(p,r)
 Q=s.div(s.expand(fvr*f-fr*fv),p-r,p)[0]/(2*fr)
 assert s.expand(s.div(s.expand(fvr*f-fr*fv),p-r,p)[1])==0
 qc=s.Poly(Q,p)
 vec=[s.factor(sum(qc.coeff_monomial(p**n)*reductions[n][i]for n in range(6)))for i in range(10)]
 diag=-fvr/(2*fr)
 Rv=sum(vec[4+i]*p**i for i in range(6))
 if v==r:Rv-=1/(p-r)
 target=-fv/(2*(p-r)) if v!=r else f/(p-r)**2
 reconstructed=diag*f/(p-r)+sum(vec[i]*p**k*f for i,k in enumerate(bs))+s.diff(Rv,p)*f-Rv*s.diff(f,p)/2
 assert s.cancel(target-reconstructed)==0
 out['columns'][str(v)]=[str(a)for a in vec[:4]]+[str(s.factor(diag))]
 out['exact_primitives'][str(v)]=str(s.factor(Rv))
 print(v,out['columns'][str(v)],flush=True)
Path(__file__).with_name('moving-pole-connection.json').write_text(json.dumps(out,indent=2))
