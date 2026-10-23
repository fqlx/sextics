"""Exact source-carrying current in the full kappa gauge; no solve claimed."""
import json
import sympy as s
H,B,C,p,hB=s.symbols('H B C p hB')
k=B**3/(C*H**2)
F=-H/(p*(B+3*C*p**2)); V=F-s.Rational(1,3)
R=B*p/(B+3*C*p**2)**3; W=C*H*R; q=-p/(B+3*C*p**2)
f=C*p**3+B*p+H
alpha=-9*H/(2*B**2); beta=-H*(4*k+27)/B**2

def rem0(value):
    num=s.fraction(s.cancel(value))[0]
    return s.rem(num,f,p)==0

def dH(value):
    return s.diff(value,H)-s.diff(value,p)/(B+3*C*p**2)

def dB(value):
    return s.diff(value,B)+hB*s.diff(value,H)

checks={}
checks['q_gauge']=rem0(q-alpha*V-beta*W)
checks['q_H_simple']=rem0(dH(q)-3*(V+6*W)/(2*B**2))
A=alpha/2; D=beta/2
ell=dB(s.log(k))
# The physical B-density is independent of B, so divergence is dB of coefficient.
checks['first_component']=s.cancel(dB(A)+3*D*ell/(4*k+27)-3*hB/(4*B**2))==0
checks['second_component']=s.cancel(dB(D)-2*A*ell+(27-2*k)*D*ell/(4*k+27)-1/(C*H)-9*hB/(2*B**2))==0
checks['residual_direction']=rem0((hB/2)*dH(q)-3*hB*(V+6*W)/(4*B**2))
assert all(checks.values()),checks
print(json.dumps({'checks':checks, 'passed':sum(checks.values()),'certificate':False},indent=2))
