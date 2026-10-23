"""Checks that the physical first-current remainder returns coefficient one."""
import sympy as s
u,v,z=s.symbols('u v z')
H=1+u**6/v**2+v**2+z**6+u*z/2
C=u**3*z/(2*v)+u/3
Kb=(1+z**6)/3+7*u*z/36
W=[-u/(18*v**2),-1/(3*v),s.S(0)]
variables=[u,v,z]
divW=sum(s.diff(a,q)for a,q in zip(W,variables))
assert s.factor(divW-5/(18*v**2))==0
WH=sum(a*s.diff(H,q)for a,q in zip(W,variables))
WC=sum(a*s.diff(C,q)for a,q in zip(W,variables))
# Euler compact-connection identity: e0=-(3H/2) MH e0-C MC e0.
left_H=WH-s.Rational(3,2)*H*divW
left_C=WC-C*divW
right_H=-(H/12+Kb)/v**2-1
right_C=-(C/9+2*u/27)/v**2
assert s.factor(left_H-right_H)==0
assert s.factor(left_C-right_C)==0
print('Verified div(W omega0)=(R/v^2)-nabla_H omega0.')
print('Physical remainder carries the original class with coefficient ONE.')
print('This first current alone does not give a certificate or invertible closure.')
