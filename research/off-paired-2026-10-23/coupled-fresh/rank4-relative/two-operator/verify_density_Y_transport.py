import sympy as s
a,C,z=s.symbols('a C z')
q=3*C-s.Rational(3,2)*a*z
rho=q**3/a**2
R=-27*C**3/a+s.Rational(81,4)*C*z*z*a-s.Rational(27,16)*z**3*a*a
WR=-s.Rational(81,4)*C*C*z*z/a
assert s.cancel(s.diff(R,a)+s.diff(WR,z)-rho)==0
# Algebraic current comparison uses only the exact source constraint.
ha,hz,u0,r,w,rr=s.symbols('ha hz u0 r w rho')
w0=(-rr/6-ha*u0)/hz
J=ha*r+hz*w
S=(r*w0-w*u0)/J
ur=-rr*r/(6*J);wn=-rr*w/(6*J)
assert s.cancel(ur-u0-S*hz)==0
assert s.cancel(wn-w0+S*ha)==0
assert s.cancel(ha*ur+hz*wn+rr/6)==0
print('Exact ordinary density, source flux, and free Y-current transport passed.')
