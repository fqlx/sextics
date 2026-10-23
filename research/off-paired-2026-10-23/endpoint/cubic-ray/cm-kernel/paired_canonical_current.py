"""Canonical full two-component form of the parity-correct paired CM jet.

This checks the actual current and retains both residual rows.  No closure
or vanishing of either component is asserted.
"""
import json
from pathlib import Path
import sympy as S

p,H,B,C,h,b=S.symbols('p H B C h b',nonzero=True)
f=C*p**3+B*p+H
g=B+3*C*p**2
Delta=4*B**3+27*C*H**2
J=H*b-4*B*h**5
kappa=B**3/(C*H**2)
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
def reduce(value):
    n,d=S.fraction(S.cancel(value))
    return S.rem(S.Poly(n,p)*S.invert(S.Poly(d,p),S.Poly(f,p)),S.Poly(f,p)).as_expr()
def dh(value):
    return S.diff(value,h)+6*h**5*S.diff(value,H)+b*S.diff(value,B)

V=reduce(-H/(p*g)-S.Rational(1,3))
W=reduce(C*H*B*p/g**3)
q=reduce(p/g**2+3*H/Delta)
check('paired-tracefree-canonical-coefficients',
      reduce(q+27*H*V/(2*Delta)+2*W/(C*H)))

a=-27*B*H**2/(4*J*Delta)
d=-B/(C*J)
lam=3*J/(B*H)
check('physical-lambda-normal',dh(kappa)/kappa-lam)
check('actual-current-normalization',reduce(a*V+d*W-B*H*q/(2*J)))

# Covariant derivative must agree with literal differentiation in the cubic
# field.  This includes p_h=-(6h^5+b*p)/g.
def dh_cubic(value):
    return reduce(dh(value)-(6*h**5+b*p)*S.diff(value,p)/g)
rowV=S.factor(dh(a)+3*lam*d/(4*kappa+27))
rowW=S.factor(dh(d)-2*lam*a+(27-2*kappa)*lam*d/(4*kappa+27))
check('V-canonical-row-literal-derivative',
      reduce(dh_cubic(V)+2*lam*W))
check('W-canonical-row-literal-derivative',
      reduce(dh_cubic(W)-lam*(3*V+(27-2*kappa)*W)/(4*kappa+27)))

# A generic actual physical specialization: c=1,T=1,Vphysical=1,Y=i,
# h=1.  It satisfies all field equations with w^3=2,e=w.
# Hence H=C=1, B=5/6-i/2, b=1/3-i/2, and both residual rows are nonzero.
physical={H:S.Integer(1),C:S.Integer(1),h:S.Integer(1),
          B:S.Rational(5,6)-S.I/2,b:S.Rational(1,3)-S.I/2}
assert S.simplify(rowV.subs(physical))!=0
assert S.simplify((rowW-1/(C*H)).subs(physical))!=0
checks.append('actual-physical-nonzero-two-component-remainder')

data={
    'status':'Actual coupled paired CM current with explicitly retained nonzero residual; no certificate',
    'check_count':len(checks),'checks':checks,
    'constant_scope':'fixed characteristic-zero k; k=C for the full contract',
    'coefficient_definitions':{'b':'B_h','J':str(J),'Delta':str(Delta)},
    'current':{'A_h':str(a),'D_h':str(d),'other_directions':'zero'},
    'normal_derivative':'partial_h+6*h^5*partial_H+b*partial_B; b_h=0',
    'lambda_h':str(lam),
    'forcing':{'V':'0','W':'1/(C*H)'},
    'actual_divergence':{'V':str(rowV),'W':str(rowW)},
    'residual':{'V':str(rowV),'W':str(S.factor(rowW-1/(C*H)))},
    'gap':'Neither residual row vanishes. No mixed c/E2 correction has been found.',
}
Path(__file__).with_name('paired-canonical-current-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact canonical-current and actual nonzero-remainder checks')
