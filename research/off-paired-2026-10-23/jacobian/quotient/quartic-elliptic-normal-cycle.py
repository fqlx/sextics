"""Exact quartic elliptic companion normal-source audit, with boundary retained."""
import sympy as s
Y,G,v=s.symbols('Y G v')
E=Y**2-G
B=-2*v**4/(3*Y)
Bt=-2*v**4*Y/(3*G)
normal2=lambda P:s.diff(P,Y)/(4*Y**2)-P/(4*Y**3)
assert s.factor(normal2(B)-v**4/(3*Y**4))==0
assert s.factor(normal2(Bt))==0
assert s.factor(B-Bt-2*v**4*E/(3*Y*G))==0
# The E^-1 remainder has ordinary normal residue coefficient 1/(2Y).
first=s.factor((2*v**4/(3*Y*G))/(2*Y))
assert s.factor(first.subs(Y**2,G)-v**4/(3*G**2))==0
print('Verified B=-2v^4/(3Y) gives the exact rational normal source.')
print('Replacing 1/Y by Y/G has zero second residue and returns original source via first residue.')
print('No polynomial-companion primitive or certificate follows from this identity.')
