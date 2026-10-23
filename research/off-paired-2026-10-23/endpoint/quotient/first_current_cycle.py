"""Exact first-current residual cycle. Coefficient one prevents a primitive claim.

Retains the h/G correction via the essential v^-2 factor. It proves only
an integration-by-parts identity in the audited compact Gauss-Manin system.
"""
import sympy as s,json
from pathlib import Path
u,v,z=s.symbols('u v z');H=1+u**6/v**2+v**2+z**6+u*z/2;C=u**3*z/(2*v)+u/3
Kb=(1+z**6)/3+s.Rational(7,36)*u*z
W=[-u/(18*v**2),-1/(3*v),s.S(0)];vs=[u,v,z]
divW=s.cancel(sum(s.diff(a,x)for a,x in zip(W,vs)))
WH=s.cancel(sum(a*s.diff(H,x)for a,x in zip(W,vs)))
WC=s.cancel(sum(a*s.diff(C,x)for a,x in zip(W,vs)))
assert s.cancel(divW-s.Rational(5,18)/v**2)==0
assert s.cancel(WH-(u**6/(3*v**4)-s.Rational(2,3)-u*z/(36*v**2)))==0
assert s.cancel(WC-(u**3*z/(12*v**3)-u/(54*v**2)))==0
# Euler identity: e0=-(3H/2) MH e0-C MC e0.
current_H=s.cancel(WH-s.Rational(3,2)*H*divW)
current_C=s.cancel(WC-C*divW)
R_H=-(H/12+Kb)/v**2;R_C=-(C/9+2*u/27)/v**2
assert s.cancel(current_H-(R_H-1))==0
assert s.cancel(current_C-R_C)==0
out={'checks':5,'current':['-u/(18*v^2)','-1/(3*v)','0'],'divergence':'5/(18*v^2)','identity':'div_connection(W*omega0)=R/v^2 - nabla_H omega0','original_source_cycle_coefficient':1,'status':'not a primitive: scalar cycle coefficient is exactly one','retained_correction':'h/G=h/(v^2F), so endpoint reduction is R/v^2'}
Path(__file__).with_name('first-current-cycle-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
