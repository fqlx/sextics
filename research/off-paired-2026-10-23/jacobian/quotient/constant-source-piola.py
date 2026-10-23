"""Exact pullback of a constant-density contact field; no field W supplied."""
import sympy as s
x,y,z,u,v=s.symbols('x y z u v')
wu,wv,wz=[s.Function(a)(u,v,z)for a in ['Wu','Wv','Wz']]
W=[wu,wv,wz]
sub={u:x*y,v:y**3}
Wp=[a.subs(sub,simultaneous=True)for a in W]
V=[3*y**2*Wp[0]-x*Wp[1],y*Wp[1],3*y**3*Wp[2]]
actual=s.diff(V[0],x)+s.diff(V[1],y)+s.diff(V[2],z)
expected=3*y**3*sum(s.diff(a,q)for a,q in zip(W,[u,v,z])).subs(sub,simultaneous=True)
assert s.simplify(actual-expected)==0
Hq=1+u**6/v**2+v**2+z**6+u*z/2
Cq=u**3*z/(2*v)+u/3
Hp=1+x**6+y**6+z**6+x*y*z/2
Cp=x**3*z/2+x*y/3
assert s.factor(Hq.subs(sub,simultaneous=True)-Hp)==0
assert s.factor(Cq.subs(sub,simultaneous=True)-Cp)==0
for exprq,exprp in [(Hq,Hp),(Cq,Cp)]:
 lhs=sum(a*s.diff(exprp,q)for a,q in zip(V,[x,y,z]))
 rhs=3*y**3*sum(a*s.diff(exprq,q)for a,q in zip(W,[u,v,z])).subs(sub,simultaneous=True)
 assert s.simplify(lhs-rhs)==0
print('Verified physical V=(3y²Wu−xWv,yWv,3y³Wz).')
print('Verified div(V)=3y³ div(W) and V(H,C)=3y³ W(H,C).')
print('Thus divW=0 and 2CWH−3HWC=2/3 imply original contact equations with A=y³.')
