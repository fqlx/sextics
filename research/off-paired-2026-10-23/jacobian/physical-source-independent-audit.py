"""Independent exact source and correction audit, no certificate asserted."""
import sympy as s
x,y,z,a,H,C=s.symbols('x y z a H C')
Hxy=1+x**6+y**6+z**6+x*y*z/2
Cxy=x**3*z/2+x*y/3
q=3*C-s.Rational(3,2)*a*z
P=a**4+q**6+a**2*(z**6+q*z/2+1-H)
Pa=s.diff(P,a)
Paa=s.diff(Pa,a)
qa=s.diff(q,a)
phi=q**3/Pa
# Total coefficient derivatives on P=0 use a_H=-P_H/P_a=a^2/P_a.
aH=a**2/Pa
phiH=s.diff(phi,H)+s.diff(phi,a)*aH
expected=((2*a*q**3+3*a**2*q**2*qa)*Pa-a**2*q**3*Paa)/Pa**3
assert s.cancel(phiH-expected)==0
# Exact Jacobian J=det d(H,C,z)/d(x,y,z)=P_a/a on the physical graph.
J=s.det(s.Matrix([[s.diff(f,u) for u in (x,y,z)]for f in (Hxy,Cxy,z)]))
physical_Pa=s.cancel(Pa.subs({a:x**3,H:Hxy,C:Cxy}))
assert s.cancel(J-physical_Pa/x**3)==0
assert s.cancel(y**3/J-(phi.subs({a:x**3,H:Hxy,C:Cxy})))==0
print('Verified J=P_a/a and y^3 dx dy dz=phi dH dC dz.')
print('Verified full phi_H formula with derivative at fixed C,z.')
R=-27*C**3/a+s.Rational(81,4)*C*z**2*a-s.Rational(27,16)*z**3*a**2
res=-s.Rational(81,2)*C**2*z
assert s.cancel(phi-s.diff(R,a)*aH-res*aH/a)==0
print('Verified phi=R_H -(81/2)C^2 z (log a)_H.')
# Equivalent identity uses no logarithms and can be transported as rational 1-forms:
# phi dH = dR + res da/a, modulo dC,dz.
print('All identities use exact rational coefficients; no primitive for sigma_phys yet.')
