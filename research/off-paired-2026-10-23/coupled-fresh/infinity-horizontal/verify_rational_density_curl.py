"""Exact all-rational density transport, with its full retained remainder."""
import sympy as s
import json
from pathlib import Path
H,C,z=s.symbols('H C z')
a=s.Function('a')(H,C,z)
alpha=2*C/(3*H)
T=lambda f:s.diff(f,H)+alpha*s.diff(f,C)
theta=lambda f:C*s.diff(f,C)
curl=lambda p,q:s.diff(p,z)-T(q)
v=a*z
q=3*C-s.Rational(3,2)*v
rho=q**3/a**2
phi=rho*s.diff(a,H)
Pe=rho*T(v)/2
Qe=rho*s.diff(v,z)/2
J=alpha*(9*q**2*s.diff(v,z)/(2*a**2)-rho*s.diff(a,C))
assert s.cancel(phi-curl(Pe,Qe)-J)==0
K=Qe-H*J
Ksmall=q**2*(q/2-3*C)*s.diff(v,z)/a**2+2*C*rho*s.diff(a,C)/3
assert s.cancel(K-Ksmall)==0

# Prove the source-curl identity before applying any operator B commuting
# with T, Dz and coefficients 1/H. The operator theta commutes with T,Dz;
# B need not commute with theta. This avoids hiding an integration
# assumption in a long expanded connection computation.
p=s.Function('p')(H,C,z)
r=s.Function('r')(H,C,z)
j=s.Function('j')(H,C,z)
f=curl(p,r)+j
Pc=-theta(p)/(9*H)
Qc=-theta(r)/(9*H)-f/6
rem=theta(r-H*j)/(9*H**2)
assert s.cancel(s.diff(f,H)/6-curl(Pc,Qc)-rem)==0

# Bare Euler primitive: Ea=a, Ez=-z at fixed C, so E(q)=0.
A,Z,CC=s.symbols('A Z CC')
qq=3*CC-s.Rational(3,2)*A*Z
rr=qq**3/A**2
Ra=-qq**3/(2*A)
Wz=Z*qq**3/(2*A**2)
assert s.cancel(s.diff(Ra,A)+s.diff(Wz,Z)-rr)==0
E=lambda f:A*s.diff(f,A)-Z*s.diff(f,Z)
HH=A**2+qq**6/A**2+Z**6+qq*Z/2+1
JJ=E(HH)
assert s.cancel(JJ-(2*A**2-2*qq**6/A**2-6*Z**6-qq*Z/2))==0
assert s.cancel(2*JJ+E(JJ)-(8*A**2+24*Z**6-qq*Z/2))==0

result={'status':'passed','exact_symbolic_groups':6,
        'scope':'Rational density/current transport, including a retained source remainder; not a primitive of the endpoint source.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
