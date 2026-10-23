"""Exact singularity inventory of the normal weighted exceptional surface."""
from pathlib import Path
import sympy as s,json
H=Path(__file__).parent;h,u=s.symbols('h u');k=9*h-5
A0=s.Rational(1875,56)*k**2*(153*h*h+180*h+125);A1=6250*k*k;D=23152500;G=-590625*(h+1)*k;C=-16537500;E=-s.Rational(826875,8)*k*k;F=-s.Rational(10125,64)*k**4
J=C*u*u+E*u+F;K=A0+A1*u-G*G/s.Integer(4*D)
mod=s.Poly(h**6-s.Rational(171,196),h)
def rem(f):return s.Poly(s.cancel(f),h).rem(mod).as_expr()
def unit(f):return s.gcd(s.Poly(rem(f),h),mod).degree()==0
res=s.factor(s.resultant(J,K,u));disc=s.factor(s.discriminant(J,u));quartic=s.factor(A0*D**2/C**2)
u0=-s.Rational(3,1120)*k*k
b0=s.factor(-s.diff(J,u).subs(u,u0)/A1)
assert s.simplify(K.subs(u,u0))==0 and s.simplify(J.subs(u,u0))==0
assert b0==s.Rational(189,80)
assert all(unit(f)for f in [k,A0,A1,D,C,disc,quartic,b0])

result=dict(coefficientField='QQ(h),h6=171/196',etaOneChart='After eliminating z by its critical equation, g=b*(J(u)+b*K(u)).',J=str(J),K=str(s.factor(K)),resultantJK=str(res),commonRootU=str(u0),extraPointB=str(b0),extraPointZ=str(s.factor(-G*b0/(2*D))),extraPointType='A1: reduced local quadratic is b0*delta_u*(C*delta_u+A1*delta_b), nondegenerate.',etaChartSingularities='Two b=z=0 points, J(u)=0; nonzero J discriminant gives nondegenerate Hessian, typeA1.',Jdiscriminant=str(disc),uOneChart='At b=z=eta=0, (b,eta) Hessian has rank2. Splitting eliminates these variables; leading residual z4 has nonzero coefficientA0*D²/C², hence typeA3.',z4Coefficient=str(quartic),weightTwoLine='On u=eta=0, derivative_u=A1*b², derivative_eta=D*z²+G*z*b+A0*b² have no common projective zero. The coarse surface is smooth there.',singularityInventory={'A1':3,'A3':1},allUnitsCheckedExactly=True,scope='Exact exceptional-surface classification; its use for rationality of the full weighted threefold blowup requires the stated deformation/inversion-of-adjunction argument.')
(H/'T0_surface_singularities.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
