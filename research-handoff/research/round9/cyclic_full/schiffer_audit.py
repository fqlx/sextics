"""Exact eta component of the actual-source Schiffer/Higgs comparison."""
from pathlib import Path
import sympy as s,pickle,json,time
from sympy.polys.matrices import DomainMatrix
root=Path(__file__).parent;start=time.monotonic()
data=pickle.loads((root/'actual_fast.pickle').read_bytes())
W,h,t,L,r,x=data['symbols'];z=s.symbols('z');vv=(W,h,t);C=data['curve']
rows=[(i,j,k)for i in range(9)for j in range(9)for k in range(5)if i+j+2*k==8 and i%3==0]
def mon(e):return W**e[0]*h**e[1]*t**e[2]
labs=[(i,e)for i,wt,ch in [(0,3,1),(1,3,0),(2,4,0)]for e in [(a,b,c)for a in range(wt+1)for b in range(wt+1)for c in range(wt//2+1)if a+b+2*c==wt and a%3==ch]]
J=s.Matrix([[s.Poly(s.diff(C,vv[i])*mon(e),*vv).coeff_monomial(mon(rr))for i,e in labs]for rr in rows])
eta=data['eta'][0];A=(x*J.row_join(s.Matrix([int(mon(rr)==eta)for rr in rows]))).applyfunc(s.expand)
DM=DomainMatrix.from_Matrix(A);iv,de=DM.inv_den();iv=iv.to_Matrix();de=DM.domain.to_sympy(de)
assert all(s.expand(v)==0 for v in A*iv-de*s.eye(A.rows))
def eta_component(P):
    v=s.Matrix([s.Poly(s.expand(P),*vv).coeff_monomial(mon(rr))for rr in rows])
    return s.factor((iv[-1,:]*(x*v))[0]/de)
S0=h**4*(t-z*h*h)**2;S1=h*h*t*(t-z*h*h)**2
eta0,eta1,diff=[eta_component(P)for P in (S0,S1,S1-z*S0)]
assert s.cancel(diff-eta1+z*eta0)==0
source=pickle.loads(Path('/workspace/research/round8/coupled_source/source_model.pickle').read_bytes());sym=source['symbols']
physz=source['B']*source['R']/(3*source['S']-source['B']*source['R'])
physical={L:source['L'],r:source['r'],x:source['x'],z:physz};samples=[]
for pt in [(1,2,3),(2,1,3),(2,3,1)]:
    sub=dict(zip((sym['a'],sym['b'],sym['v']),pt));pars={p:s.cancel(v.subs(sub))for p,v in physical.items()}
    val=s.cancel(diff.subs(pars));assert val
    samples.append(dict(point=pt,value=str(val),nonzero=True))
ans=dict(source0=str(S0),source1=str(S1),eta0=str(eta0),eta1=str(eta1),difference=str(diff),
         difference_numerator_factorization=str(s.factor(s.numer(diff))),
         schiffer_at_T_equals_z_requires='eta(S1)-z*eta(S0)=0',
         exact_generic_difference_nonzero=bool(diff),physical_samples=samples,seconds=time.monotonic()-start,
         scope='Failure of this source to be the claimed single Schiffer channel at T=z; no support or certificate no-go.')
(root/'schiffer_audit.json').write_text(json.dumps(ans,indent=2)+'\n')
(root/'schiffer_audit.pickle').write_bytes(pickle.dumps(dict(symbols=(L,r,x,z),eta0=eta0,eta1=eta1,difference=diff,all_monomial_eta=[s.factor(x*iv[-1,i]/de)for i in range(len(rows))],monomials=[mon(e)for e in rows])))
print(json.dumps(ans,indent=2))
