"""Exact normalized model and needed character on the six J=0 exceptional curves."""
from pathlib import Path
import sympy as S,json
v,e,H=S.symbols('v ell H')
mod=e*e-e+1
def er(f):
 n,d=map(S.expand,S.fraction(S.cancel(f)))
 return S.rem(n,mod,e)/S.rem(d,mod,e) if S.degree(d,e)==0 else S.cancel(S.invert(d,mod,e)*S.rem(n,mod,e))
T=-5*H*H/324
C=S.factor(T**3-H**4*T/3888+H**6/629856)
assert C==H**6/531441
f=-4*(1+v*v)*(e+(e-1)*v*v)
a,b,c,d,z=S.Poly(S.expand(f),v).all_coeffs()
I=er(12*a*z-3*b*d+c*c)
J=er(72*a*c*z+9*b*c*d-27*a*d*d-27*b*b*z-2*c**3)
jj=er(6912*I**3/(4*I**3-J**2));assert S.cancel(jj-54000)==0
basis=[]
for j in range(1,6):
 for i in range((2*j-4)//3+1):
  assert 5-j>=0 and 2*j-3*i-4>=0
  basis.append({'i':i,'j':j,'differential':f'v^{i} dv/y^{j}','U_odd':bool(j%2)})
assert len(basis)==7 and sum(x['U_odd']for x in basis)==4
out={'chart':'j=1+q6; H=j2*h,T=j4*t,V=j2*U, v unchanged',
 'leading_H':'q3/54','leading_T':'-5H2/324','constant_cubic':str(C),
 'normalization_coordinate':'y=H/(9V)', 'curve':f'y6={S.expand(f)}',
 'genus':7,'basis':basis,'binary_quartic_I':str(I),'binary_quartic_J':str(J),
 'elliptic_quotient':'Y=y3, Y2=quartic(v)','elliptic_j':str(jj),
 'odd_Jacobian_up_to_isogeny':'E(j=0)^4',
 'proof':'Odd j3 gives the CM elliptic quotient j54000. Odd primitive-sixth character j5 has holomorphic dimension3 while its conjugate j1 has dimension0, so the Q(sqrt(-3))-factor has pure signature(3,0) and is isogenous to E(j=0)^3. Even factors are not asserted CM.',
 'scope':'The local exceptional curve and its odd Jacobian are verified. No global extension of these local forms is asserted.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
