"""Construct a source-specific Schiffer evaluation section and exact Jacobian lift.
This establishes an infinitesimal relative-curve identity, not a Hodge certificate.
"""
from pathlib import Path
import sympy as s,pickle,json,time
from sympy.polys.matrices import DomainMatrix
HERE=Path(__file__).parent;start=time.monotonic()
base=Path('/workspace/research/round9/cyclic_full')
data=pickle.loads((base/'actual_fast.pickle').read_bytes())
prior=pickle.loads((base/'schiffer_audit.pickle').read_bytes())
W,h,t,L,r,x=data['symbols'];z=prior['symbols'][-1];vv=(W,h,t);C=data['curve'];eta=data['eta'][0]
e0,e1=prior['eta0'],prior['eta1']
n0,d0=s.fraction(e0);n1,d1=s.fraction(e1)
D=s.lcm(d0,d1);N0=s.cancel(D*e0);N1=s.cancel(D*e1)
assert s.denom(N0)==s.denom(N1)==1
Teff=s.cancel(N1/N0)
S0=h**4*(t-z*h*h)**2;S1=h*h*t*(t-z*h*h)**2
P=s.expand(N0*S1-N1*S0)
rows=[(i,j,k)for i in range(9)for j in range(9)for k in range(5)if i+j+2*k==8 and i%3==0]
def mon(e):return W**e[0]*h**e[1]*t**e[2]
labs=[(i,e)for i,wt,ch in [(0,3,1),(1,3,0),(2,4,0)]for e in [(a,b,c)for a in range(wt+1)for b in range(wt+1)for c in range(wt//2+1)if a+b+2*c==wt and a%3==ch]]
J=s.Matrix([[s.Poly(s.diff(C,vv[i])*mon(e),*vv).coeff_monomial(mon(rr))for i,e in labs]for rr in rows])
A=(x*J.row_join(s.Matrix([int(mon(rr)==eta)for rr in rows]))).applyfunc(s.expand)
DM=DomainMatrix.from_Matrix(A);iv,de=DM.inv_den();iv=iv.to_Matrix();de=DM.domain.to_sympy(de)
v=s.Matrix([s.Poly(P,*vv).coeff_monomial(mon(rr))for rr in rows])
coeff=[s.cancel(y/de)for y in iv*(x*v)]
assert coeff[-1]==0
Q=[sum(coeff[j]*mon(e)for j,(i,e)in enumerate(labs)if i==k)for k in range(3)]
# Exact coefficient equality, not point tests.
assert all(s.cancel(y)==0 for y in J*s.Matrix(coeff[:-1])-v)
Qden=s.lcm([s.denom(s.cancel(y))for y in coeff[:-1]])
assert s.expand(P-h*h*(N0*t-N1*h*h)*(t-z*h*h)**2)==0
out={'symbols':(W,h,t,L,r,x,z),'curve':C,'N0':N0,'N1':N1,'common_eta_denominator':D,'T_effective':Teff,'graph_support':N0*t-N1*h*h,'relative_source_identity_numerator':P,'Q':Q,'Qdenominator':Qden,'identity':'h²*(N0*t-N1*h²)*(t-z*h²)^2 = sum_i Q_i*C_i; exact over QQ(L,r,x,z).','scope':'A source-specific relative-Jacobian identity and evaluation/Higgs channel only. No global physical support, holomorphic2form, Gysin serving statement or certificate is proved.'}
(HERE/'effective_schiffer.pickle').write_bytes(pickle.dumps(out))
ans={'N0_terms':len(s.Poly(N0,L,r,x,z).terms()),'N1_terms':len(s.Poly(N1,L,r,x,z).terms()),'N0_degrees':s.Poly(N0,L,r,x,z).degree_list(),'N1_degrees':s.Poly(N1,L,r,x,z).degree_list(),'T_effective':'N1/N0','relative_Jacobian_identity_exact':True,'eta_component_zero':True,'Q_denominator':str(s.factor(Qden)),'source_binding':'The full actual Higgs covector for deformation h²(t-z*h²)^2 has evaluation kernel omega1-(N1/N0)*omega0.','scope':out['scope'],'seconds':round(time.monotonic()-start,3)}
(HERE/'effective_schiffer.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
