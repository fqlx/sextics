import sympy as S
v,u,ell,J,G,bd,p0,p1,n0,n1,n2,a,b=S.symbols('v u ell J G bd p0 p1 n0 n1 n2 a b',nonzero=True)
E=2*p0+p1*v;N=n0+n1*v+n2*v*v;F=ell*u**3+J;g=3*ell*u*u
# Work in the free algebra K[v]/(v^3+J/ell). The trace is three times the constant coefficient.
def red(P): return S.Poly(S.rem(S.together(P),v**3+J/ell,v),v)
def tr(P):return S.factor(3*red(P).nth(0))
invuv=(u*u+u*v+v*v)*ell/F
assert S.factor(red((u-v)*invuv).as_expr()-1)==0
# On the cubic cover, S0 simplifies to -2bd E*v/(9J²).
S0=-2*bd*E*v/(9*J**2); w=3*J*F*N/(G**3*E*(u-v))
assert S.factor(tr(-2*bd*F*N*v*invuv/(3*J*G**3))-2*bd*(n0+n1*u+n2*u*u)/G**3)==0
# Independently check proposed E^{-1} and then its traced current.
e=2*p0;D=e**3-p1**3*J/ell
invE=(e*e-e*p1*v+p1*p1*v*v)/D
assert S.factor(red(E*invE).as_expr()-1)==0
# v^-1 = -ell*v²/J and v^-2 = -ell*v/J.
beta=-ell*(a*v*v+b*v)/J
q=red(N*beta*invE);q0,q1,q2=[S.factor(q.nth(i)) for i in range(3)]
Q0=a*n1+b*n2; Q1=a*n2-ell*b*n0/J; Q2=-ell*(a*n0+b*n1)/J
R0=(e**2*Q0+(e*p1*Q2-p1**2*Q1)*J/ell)/D
R1=(e**2*Q1-e*p1*Q0-p1**2*Q2*J/ell)/D
R2=(e**2*Q2-e*p1*Q1+p1**2*Q0)/D
assert all(S.factor(x-y)==0 for x,y in zip((q0,q1,q2),(R0,R1,R2)))
L=tr(q.as_expr()*invuv)
formula=1/F*(g*(q0+q1*u+q2*u*u)-3*F*(q1+u*q2))
assert S.factor(L-formula)==0
tracecurrent=S.factor(3*J*F*L/G**3)
assert S.factor(tracecurrent-3*J/G**3*(g*(q0+q1*u+q2*u*u)-3*F*(q1+u*q2)))==0

print('PASS exact source-matched trace via quotient-ring inverse; conditions ell*J*G*F*D !=0')
print('Trace current = 3J*F/G^3 * Tr[(N beta/E)/(u-v)]')
