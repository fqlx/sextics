import sympy as s
p,H,B,C=s.symbols('p H B C')
f=C*p**3+B*p+H; g=B+3*C*p**2; Delta=4*B**3+27*C*H**2
q=-p/g; V=-H/(p*g)-s.Rational(1,3); W=C*H*B*p/g**3
# A low denominator reconstruction of the universal coefficient derivative.
a,b=s.symbols('alpha beta')
num=s.fraction(s.cancel(q-a*V-b*W))[0]
rem=s.rem(num,f,p)
sol=s.solve(s.Poly(rem,p).coeffs(),(a,b),dict=True)[0]
print(sol)
