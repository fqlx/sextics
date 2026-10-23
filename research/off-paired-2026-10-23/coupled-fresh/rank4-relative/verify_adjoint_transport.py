"""Generic Jacobian-aware horizontal adjoint transport; no primitive claim."""
import sympy as s

a,C,tau=s.symbols('a C tau')
H=s.Function('H')(a,C)
Ha=s.diff(H,a); h=s.diff(H,C)
k=2*C/(3*H); r=1-k*h
rho=Ha/tau**2; beta=tau**2/r
coords=(a,C,tau)
# tau^3=H. These rational vector fields preserve this relation.
def op(expr,vec):
    return sum(s.diff(expr,q)*v for q,v in zip(coords,vec))
Tvec=(r/Ha,k,tau/(3*H))
Bvec=(-tau**2*h/Ha,tau**2,0)
deltavec=(0,1,tau*h/(3*H))
def T(expr):return op(expr,Tvec)
def B(expr):return op(expr,Bvec)
def delta(expr):return op(expr,deltavec)
def simp(expr):return s.cancel(expr)
checks=[]
checks.append(simp(T(H)-1)==0)
checks.append(simp(B(H))==0)
checks.append(simp(delta(H)-h)==0)
for v,w in zip(Tvec,Bvec):checks.append(simp(T(w)-B(v))==0)
# At fixed tau branch, rho is the induced two-coordinate volume density.
# Divergence uses physical derivatives of tau, not independent tau partials.
def da(expr):return s.diff(expr,a)+s.diff(expr,tau)*tau*Ha/(3*H)
def dc(expr):return s.diff(expr,C)+s.diff(expr,tau)*tau*h/(3*H)
checks.append(simp(da(rho*Tvec[0])+dc(rho*Tvec[1]))==0)
checks.append(simp(da(rho*Bvec[0])+dc(rho*Bvec[1]))==0)
F=s.Function('F')(a,C,tau)
def calD(expr):return delta(rho*beta*expr)/rho
checks.append(simp(B(F)-calD(F)+T(beta*h*F))==0)
K2=beta*h*calD(F)+B(beta*h*F)
checks.append(simp(B(B(F))-calD(calD(F))+T(K2))==0)
assert all(checks),checks
print(f'{len(checks)} exact generic horizontal-transport checks passed')
