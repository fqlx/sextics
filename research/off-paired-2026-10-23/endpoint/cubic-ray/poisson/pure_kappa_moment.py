"""Small exact algebra for the pure-component kappa moment obstruction.

The accompanying note supplies the Hodge argument and restricted scope.
This is not an obstruction to the complete two-component current.
"""
import sympy as S,json
from pathlib import Path
t,x,a,w,u,v=S.symbols('t x a w u v')
H=t**6+x**6+a**6;C=w**6+u**6+v**6
B=t**3*x*u*w/2+x**3*a*u*v/2+t**2*x*a*v*w/3
N=S.expand(t**3*w**3*B**3)
selected=0
for ex,co in S.Poly(N,t,x,a,w,u,v).terms():
 if ex[4]%6==3 and ex[5]%6==3:
  selected+=co*t**ex[0]*x**ex[1]*a**ex[2]*w**ex[3]*u**ex[4]*v**ex[5]
expected=t**3*x**9*a**3*w**3*u**3*v**3/8
assert S.expand(selected-expected)==0
lift=t**3*x**4*a**3/6
assert S.expand(lift*S.diff(H,x)-t**3*x**9*a**3)==0
reduced=S.diff(lift,x)/2
assert S.expand(reduced-t**3*x**3*a**3/3)==0
proper=S.expand(reduced*w**3*u**3*v**3/8)
assert proper==t**3*x**3*a**3*w**3*u**3*v**3/24
assert all(e<5 for e in S.Poly(proper,t,x,a,w,u,v).monoms()[0])
data={'checks':5,'projected_numerator':str(selected),'H_pole3_jacobian_lift_x':str(lift),
 'H_pole2_numerator':str(reduced),'product_H02_monomial':str(proper),
 'necessary_form':'B^3/(H^3 C^2) dx da du dv',
 'pure_A_identity':'div(kappa*A)=-B^3/(2H^3C^2)',
 'pure_W_identity':'div(kappa*Bvec)=B^3/(H^3C^2)',
 'scope':'pure-A and pure-W current restrictions, including finite extensions; full two-component system remains open',
 'status':'exact algebra checked; proper-residue argument recorded in note'}
Path(__file__).with_name('pure-kappa-moment-results.json').write_text(json.dumps(data,indent=2));print('Passed5 exact Fermat moment checks')
