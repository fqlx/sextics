"""Exact ruling-normal-function differential with all finite/infinity residues."""
import sympy as s,json
from pathlib import Path
A,B,Cp,D,E,T,a,b,q,rho,L,c0,u=s.symbols('A B Cp D E T a b q rho L c0 u',nonzero=True)
C=Cp+D*D/(4*A)
Q=A*a*a+B*b*b+C*q*q+D*a*q+E*q+T
X=a+D*q/(2*A);Y=q+E/(2*Cp)
h=D*E/(4*A*Cp)
# On Q, rho²=(E²/(4Cp)−T)/B. Test d beta0 in centered coordinates.
x,y=s.symbols('x y')
f=-y/(2*B*(b+rho));g=x/(2*B*(b+rho))
def Dx(v):return s.diff(v,x)-A*x*s.diff(v,b)/(B*b)
def Dy(v):return s.diff(v,y)-Cp*y*s.diff(v,b)/(B*b)
def reduce_center(v):
 num,den=s.fraction(s.cancel(v));rem=s.rem(num,s.Poly(A*x*x+Cp*y*y+B*b*b-B*rho*rho,x),x)
 return s.cancel(rem/den)
checks=[]
checks.append(reduce_center(Dx(g)-Dy(f)-1/(2*B*b))==0)
# Finite ruling residues: beta=(2LCp/rho)beta0=−(b−rho)/(2rho)dlog R.
lineRatio=(y-L*x)/(y+L*x)
dlog_x=s.diff(lineRatio,x)/lineRatio
dlog_y=s.diff(lineRatio,y)/lineRatio
# Relation L²=−A/Cp.
for left,right in [(-y/(2*B*(b+rho)),-(b-rho)*dlog_x/(4*L*Cp)),(x/(2*B*(b+rho)),-(b-rho)*dlog_y/(4*L*Cp))]:
 expr=s.cancel(left-right);num,den=s.fraction(expr)
 num=s.rem(num,s.Poly(L*L+A/Cp,L),L).as_expr()
 num=s.rem(s.together(num).as_numer_denom()[0],s.Poly(A*x*x+Cp*y*y+B*b*b-B*rho*rho,x),x)
 checks.append(s.cancel(num)==0)
checks.append(s.cancel((-(b-rho)/(2*rho)).subs(b,-rho)-1)==0)
# Actual tangent derivations on the complete intersection.
Qa=s.diff(Q,a);Qb=s.diff(Q,b);Qq=s.diff(Q,q);J=a*Qa-b*Qb
av=-a*q/J;bv=b*q/J
aq=(-a*Qq-3*q*q*Qb)/J;bq=(b*Qq+3*q*q*Qa)/J
checks.append(s.cancel(b*av+a*bv)==0)
checks.append(s.cancel(Qa*av+Qb*bv+q)==0)
checks.append(s.cancel(b*aq+a*bq-3*q*q)==0)
checks.append(s.cancel(Qa*aq+Qb*bq+Qq)==0)
# Infinity residues in projective chart a=1,q=u,t=u³/b(u).
# beta normalized coefficient has an exact expansion depending only on b(0).
b0,b1,b2=s.symbols('b0 b1 b2',nonzero=True);bs=b0+b1*u+b2*u*u
ja=E/(2*Cp)
gamma=(bs*bs/u**6+3*ja*bs/u**4+(2*h*bs-ja*s.diff(bs,u))/u**3-h*s.diff(bs,u)/u**2)
beta=L*Cp/(B*rho)*gamma/(bs*bs/u**3+rho)
res=s.residue(beta,u,0)
cinf=3*L*E/(2*B*rho*b0)
checks.append(s.cancel(res-cinf)==0)
# q_aff=b(u)/u²,a_aff=b(u)/u³,b_aff=b(u)²/u³.
af=bs/u**3;bf=bs*bs/u**3;qf=bs/u**2
Jf=2*A*af*af+D*af*qf-2*B*bf*bf
omega=s.cancel(qf*qf*s.diff(qf,u)/Jf)
resw=s.factor(s.residue(omega,u,0))
# Substitute B*b0²=−A only after extracting residue.
checks.append(s.cancel((resw+b0/(2*A)).subs(B,-A/b0**2))==0)
assert all(checks),checks
out={'checks':len(checks),'passed':True,'finite_residues':'+1,-1 on two ruling degree3 divisors','infinity_residues':'±c_inf removed by c_inf omega_inf','source_match':'qt-source is −D_E eta_b; not yet identified with compact variation of beta_hat','certificate':False}
Path(__file__).with_name('ruling-third-kind-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
