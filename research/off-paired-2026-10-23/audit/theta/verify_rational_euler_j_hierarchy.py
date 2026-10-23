#!/usr/bin/env python3
"""Literal rational third j-primitive of the normalized Euler source.

Finite and infinity poles of all displayed forms are retained. This is not
a density-weighted source closure or a compact-only reduction.
"""
import json
from pathlib import Path
import sympy as s

i,j,v,x,y=s.symbols('i j v x y',nonzero=True)
V=i*x*x+x+1
P=y**4+v*V*y*y+j*v*x**4*y+v*x**6
J=2*v*x**6/y**2+j*v*x**4/y-2*y*y
yj=v*x**4/J
f=v*y/J
def dj(z):return s.diff(z,j)+yj*s.diff(z,y)
def dn(z):
    return -2*i*s.diff(z,i)-j*s.diff(z,j)+6*v*s.diff(z,v)+x*s.diff(z,x)+(3*y+v*x*y/J)*s.diff(z,y)
checks={}
def check(name,z):
    num=s.cancel(z).as_numer_denom()[0]
    remainder=s.rem(num,P,y)
    assert remainder==0,(name,remainder)
    checks[name]=True

U1=-v*y*y/(x**3*J)
U2=-y**3/(3*x**7)
U3=-y*y/(6*x**5)+V*y**4/(12*x**11)+y**6/(6*v*x**11)
Psi1=y*y/(2*x**4)
Psi2=-3*y**5/(10*v*x**8)-V*y**3/(6*x**8)+y/(2*x*x)
R3=-V*y*y/(3*x**6)+(V*V/(24*x**12)-9/(20*v*x**6))*y**4+2*V*y**6/(15*v*x**12)+9*y**8/(80*v*v*x**12)
check('literal source moment first primitive',dj(Psi1)-f)
check('literal source moment second primitive',dj(Psi2)-Psi1)
check('raw third moment log derivative retained',dj(R3)+yj/(2*y)-Psi2)
# Dnorm acts on a coefficient times dx by (dn(coefficient)+coefficient)dx.
check('first normalized Euler primitive',U1-(2*Psi1-dn(Psi1)))
check('second normalized Euler primitive',U2-(Psi2-dn(Psi2)))
# The third log term cancels exactly in (1-Dnorm), leaving this rational form.
check('third normalized Euler primitive log cancellation',U3-(-dn(R3)-(3*y+v*x*y/J)/(2*y))-s.Rational(3,2))
check('literal j derivative U3 equals U2',dj(U3)-U2)
check('literal j derivative U2 equals U1',dj(U2)-U1)
check('literal j derivative U1 equals full normalized Euler source',dj(U1)-(3*f-dn(f)))
out={'status':'passed literal rational Euler j hierarchy; full density correction open',
 'curve':str(P),'Jbar':str(J),'Dnorm':'Dnative+Lie_(x partial_x)',
 'U1':str(U1)+' dx','U2':str(U2)+' dx','U3':str(U3)+' dx',
 'literal_chain':'partial_j U3=U2, partial_j U2=U1, partial_j U1=(4-Dnorm)nu_y',
 'third_log':'Psi3=R3+(1/2)log(y) dx; (1-Dnorm) cancels the log, with -3dx/2 an exact term',
 'source_weight':'Any density t produces explicit currents and the retained residual -t_jjj U3 after three integrations by parts (with appropriate alternating signs). Full t derivatives at fixed i,v are necessary.',
 'scope':'No finite or infinity poles have been dropped. These raw forms are not asserted compact. Existing compact source U1 differs by an explicit rational exact fiber term. No certificate.',
 'checks':checks,'count':len(checks)}
p=Path(__file__).with_name('rational-euler-j-hierarchy-results.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'pass':True,'checks':len(checks),'output':str(p)}))
