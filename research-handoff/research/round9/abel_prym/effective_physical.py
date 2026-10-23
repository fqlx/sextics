"""Native exact physical pullback of the source-specific effective marked point."""
from pathlib import Path
import sympy as s,pickle,json,time
from flint import fmpq,fmpq_mpoly_ctx
HERE=Path(__file__).parent;start=time.monotonic()
data=pickle.loads((HERE/'effective_schiffer.pickle').read_bytes());W,h,t,L,r,x,z=data['symbols']
ctx=fmpq_mpoly_ctx.get(('a','b','v'));a,b,v=ctx.gens();c=fmpq(5,7)
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
A=3*S-B*R;H=27*P*S*S-9*Q*R*S+2*R**3;J=3*S*Q-R*R
n0=s.Poly(data['N0'],L,r,x,z).as_dict();n1=s.Poly(data['N1'],L,r,x,z).as_dict()
Aexp=max(2*i+j+k+l for i,j,k,l in list(n0)+list(n1))
Bexp=max(j-3*k-l for i,j,k,l in list(n0)+list(n1))
def sub(poly):
 out=ctx.constant(0)
 for(i,j,k,l),coeff in poly.items():
  out+=fmpq(str(coeff))*fmpq(3)**(k-i)*H**i*J**j*R**l*A**(Aexp-2*i-j-k-l)*B**(Bexp-j+3*k+l)
 return out
N0,N1=sub(n0),sub(n1)
g=N0.gcd(N1);N0//=g;N1//=g
# t_old/h² = alpha*T_eff+beta, alpha=A/(3SB), beta=-R/(3S).
num=A*N1-B*R*N0;den=3*S*B*N0
gt=num.gcd(den);num//=gt;den//=gt
# New section is t_old=num/den; its affine graph is den*y²-num.
def payload(poly):return{tuple(map(int,e)):str(c)for e,c in poly.to_dict().items()}
packet={'variables':('a','b','v'),'T_effective_canonical':{'num':payload(N1),'den':payload(N0)},'t_old_over_h2':{'num':payload(num),'den':payload(den)}}
(HERE/'effective_physical.pickle').write_bytes(pickle.dumps(packet))
coeffs=list(num.to_dict())+list(den.to_dict());maxab=max(e[0]+e[1]for e in coeffs);maxv=max(e[2]for e in coeffs)
out={'N0_pullback_terms':len(N0.to_dict()),'N1_pullback_terms':len(N1.to_dict()),'t_old_numerator_terms':len(num.to_dict()),'t_old_denominator_terms':len(den.to_dict()),'t_old_numerator_degrees':list(map(int,num.degrees())),'t_old_denominator_degrees':list(map(int,den.degrees())),'homogenizing_ab_degree':maxab,'homogenizing_v_degree':maxv,'physical_graph_degree_before_coordinate_factor_removal':maxab+maxv+2,'graph_formula':'den(Y0/Y2,Y1/Y2,X1/X0)*Y2²-num(Y0/Y2,Y1/Y2,X1/X0)*X0²=0','scope':'Exact source-specific point-graph pullback. No physical E2 or Gysin-serving claim.','seconds':round(time.monotonic()-start,3)}
(HERE/'effective_physical.json').write_text(json.dumps(out,indent=2,default=int)+'\n');print(json.dumps(out,indent=2,default=int))
