import sympy as s
A,H,C,z=s.symbols('a H C z')
q=3*C-s.Rational(3,2)*A*z
P=A**4+q**6+A**2*(z**6+q*z/2+1-H)
Pa=s.diff(P,A)
R=-27*C**3/A+s.Rational(81,4)*C*z**2*A-s.Rational(27,16)*z**3*A**2
residue=-s.Rational(81,2)*C**2*z
# Differential along P=0, holding C,z fixed has a_H=a^2/P_a.
identity=s.factor(q**3-s.diff(R,A)*A**2-residue*A)
assert identity==0, identity
print('Exact identity q^3=R_a*a^2 -(81/2)C^2*z*a verified.')
print('R =',R)
print('phi = partial_H(R) -(81/2)C^2*z*partial_H(log(a)).')
