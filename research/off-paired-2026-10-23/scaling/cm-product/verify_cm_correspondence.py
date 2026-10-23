#!/usr/bin/env python3
"""Exact CM correspondence identities; no exactness assertion."""
import json
import sympy as s
x,y,n,w,b1,b2,b3=s.symbols('x y n w b1 b2 b3', nonzero=True)
q=x*y
U=q**-2
V=(x**6-y**6)/q**3
# Differentiate on x^6+y^6=1, using dy/dx=-x^5/y^5.
d1=lambda f:s.diff(f,x)-x**5/y**5*s.diff(f,y)
d2=lambda f:s.diff(f,n)-n**5/w**5*s.diff(f,w)
reduce=lambda f:s.rem(s.Poly(s.together(f).as_numer_denom()[0],y),s.Poly(y**6+x**6-1,y)).as_expr()
B=b1*x*n+b2*x**3*y*n*w+b3*x*y*w
checks={
 'elliptic_equation':s.factor(V**2-U**3+4).subs(y**6,1-x**6)==0,
 'differential_pullback':reduce(d1(U)-2*V/y**5)==0,
 'dual_U':reduce(y**5*d1(U)-2*V)==0,
 'dual_V':reduce(y**5*d1(V)-3*U**2)==0,
 'coupling_reconstruction':s.expand(B-(b1*x*n+b2*(x*y)*(n*w)*x**2+b3*(x*y)*(n*w)/n))==0,
 'first_coupling_derivative':s.expand(y**5*d1(B)-(b1*n*y**5+b2*n*w*x**2*(3*y**6-x**6)+b3*w*(y**6-x**6)))==0,
 'second_coupling_derivative':s.expand(w**5*d2(B)-(b1*x*w**5+b2*x**3*y*(w**6-n**6)-b3*x*y*n**5))==0,
}
# The degree-12 deck group has generators a:(x,y)->(zeta*x,zeta^-1*y)
# and j:(x,y)->(y,-x). The j relation and invariant U,V use only signs.
checks['j_fixes_U']=s.factor(U.subs({x:y,y:-x},simultaneous=True)-U)==0
checks['j_fixes_V']=s.factor(V.subs({x:y,y:-x},simultaneous=True)-V)==0
assert all(checks.values()), checks
print(json.dumps({'all_passed':True,'checks':checks},indent=2))
