"""Exact constant elliptic target for the invariant boundary differential."""
from pathlib import Path
import json
import sympy as s

u,y,D=s.symbols('u y D')
X=(2*(y+1)-u)/u**2
Y=((X**2-4*D)*u+X)/2
quartic=y*y-D*u**4+u-1
assert s.rem(s.together(Y*Y-X**3+4*D*X-D).as_numer_denom()[0],quartic,y)==0
dX=s.diff(X,u)+s.diff(X,y)*(4*D*u**3-1)/(2*y)
assert s.rem(s.together(y*dX+Y).as_numer_denom()[0],quartic,y)==0

out={
 'boundary_curve':'xi^2=11664*(1+q^6)^4-q^6',
 'quotient':'u=1+q^6,y=xi; y^2=11664*u^4-u+1',
 'Weierstrass':'Y^2=X^3-46656*X+11664',
 'X':str(X),
 'Y':str(Y),
 'inverse_u':'(2*Y-X)/(X^2-46656)',
 'differential':'dX/Y=-du/y=-6*q^5*dq/xi',
 'j':str(s.cancel(1728*256*11664/(s.Integer(256)*11664-27))),
 'hyperelliptic_involution':'P -> T-P, with T=(1/4,1/8) in this Weierstrass model',
 'boundary_twist_coordinate':'xi=(918330048*i/ell)*J^6*U^3/G, J=1+q^6, U^2=s/v',
 'X_boundary':'2*(918330048*i/ell)*J^4*U^3/G+(1-q^6)/J^2',
 'scope':'Exact target and boundary map only. The displayed U expression uses the boundary identity; no global elliptic point is asserted.',
}
assert s.Rational(1,8)**2==s.Rational(1,4)**3-46656*s.Rational(1,4)+11664
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
