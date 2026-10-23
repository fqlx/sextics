#!/usr/bin/env python3
"""Independent exact first jet of the proposed exceptional H20 lifts.

The derivatives are for these rational lifts. Their classes alone are not
an intrinsic Kodaira-Spencer obstruction without a relative Hodge extension.
"""
import json
from pathlib import Path
import sympy as s

a,r,z,x,b=s.symbols('a r z x b')
C=1+b**6+a**6
K=1-14*a**6+a**12
L=z**3/2+z**2*x*b/3
M=x*b/2+a*L
H=z**6+x**6+1
f1=16*M-r**2*C*K
f2=16*H+r**3*a**3*C*(1+a**6)**2
Ja=s.Matrix([[s.diff(f1,r),s.diff(f1,z)],
             [s.diff(f2,r),s.diff(f2,z)]]).subs(a,0)
rhs=-s.Matrix([s.diff(f1,a),s.diff(f2,a)]).subs(a,0)
rjet,zjet=map(s.factor,Ja.inv()*rhs)
def eqmod(expr):
 num=s.together(expr).as_numer_denom()[0]
 return s.rem(num,r**2*(1+b**6)-8*x*b,r)==0
checks={
 'z_first_jet_zero':zjet==0,
 'r_first_jet':eqmod(rjet/r-L/(x*b)),
}
# Relation on the exceptional surface, needed for simplifying rjet.
checks['exceptional_relation']=s.expand(f1.subs(a,0)-(8*x*b-r**2*(1+b**6)))==0

phi=[r/(x*b*z**2),r/(x*b*z**5),r/z**3,r*x*b/z**4]
jets=[s.factor(s.diff(v,r)*r*L/(x*b)+s.diff(v,z)*zjet) for v in phi]
checks['all_lifts_have_common_first_multiplier']=all(
 s.factor(jet-v*L/(x*b))==0 for jet,v in zip(jets,phi))
# beta=r db/b=4 db/w. Since r_x=r/(2x) at a=0,
# d(beta)=r/(2xb) dx db.
beta_derivative=r/(2*x*b)
checks['gamma3_exact_plus_mixed']=s.factor(jets[2]-beta_derivative-r/(3*z))==0
checks['partial_linear_combination']=s.factor(
 jets[3]-s.Rational(3,2)*jets[2]
 +s.Rational(3,2)*beta_derivative-r*x*b/(3*z**2))==0

# Independently enumerate anti-invariant Cprime one-forms and G one-forms.
# Cprime basis xi^(i-1) dxi/z^j, with i odd and i<2j, 1<=j<=5.
inv=[]
for j in range(1,6):
 for i in range(1,2*j):
  if i%2==0: continue
  for ell in range(3):
   if (i-2*ell-1)%12==0 and (i-2*j)%3==0:
    inv.append((i,j,ell))
checks['four_invariant_forms']=set(inv)=={(1,2,0),(1,5,0),(3,3,1),(5,4,2)}

# G differential b^(-1)db/y reduces to the nonzero character-11 class.
y=s.symbols('y')
yp=(7*b**6+1)/(2*y)
d_y_over_b=yp/b-y/b**2
g_identity=s.together((5*b**5-1/b)/(2*y)-d_y_over_b).as_numer_denom()[0]
checks['G_negative_power_reduction']=s.rem(g_identity,y**2-b**7-b,y)==0
assert all(checks.values()),checks

out={
 'status':'First-jet audit only; no closed or holomorphic global extension established.',
 'checks':checks,
 'r_a_over_r':'L/(x*b)', 'z_a':0,
 'four_invariant_lifts':[str(v) for v in phi],
 'their_actual_first_derivatives':[str(v) for v in jets],
 'exact_term':'d(4 db/w)=r dx db/(2*x*b)',
 'gamma3_mixed_term':'(4/3)*(xi dx/z) wedge (b db/y)',
 'partial_combination':'D_a(phi4-3*phi3/2)=r*x*b dx db/(3*z^2)-3*d(4db/w)/2',
 'invariant_product_basis':inv,
 'mixed_character':{
  'Cprime':'(3,5) on Fermat(12,6), fraction 3/12+5/6=13/12; H01',
  'G':'b db/y is holomorphic and pulls back the j=1728 elliptic differential'},
 'scope':'These are derivatives of particular rational extensions. They do not by '
 'themselves prove nonextension, since a legitimate relative Hodge extension may '
 'require additional rational counterterms and weighted normal transitions.',
}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
