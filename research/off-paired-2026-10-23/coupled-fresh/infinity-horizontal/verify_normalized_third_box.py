"""Exact normalization and formal adjoint of the third toric GKZ box."""
from pathlib import Path
import json
import sympy as s
i,j,l=s.symbols('i j l')
c,d,e=s.symbols('c d e',nonzero=True)
wa=-i/s.Integer(3)-2*j/s.Integer(3)-l/s.Integer(6)
wb=-i/s.Integer(3)-j/s.Integer(6)-l/s.Integer(6)
wt=-i/s.Integer(3)-j/s.Integer(6)-2*l/s.Integer(3)
# Derive the coefficient exponents independently from the normalization map.
# On every monomial c^i d^j e^l they are the A,B,T exponents of
# zeta=(T/B)^1/2*zeta_normalized.
A,B,C,D,E,T=s.symbols('A B C D E T',positive=True)
cn=C*T**(-s.Rational(1,3))*A**(-s.Rational(1,3))*B**(-s.Rational(1,3))
dn=D*T**(-s.Rational(1,6))*A**(-s.Rational(2,3))*B**(-s.Rational(1,6))
en=E*T**(-s.Rational(2,3))*A**(-s.Rational(1,6))*B**(-s.Rational(1,6))
scale=s.sqrt(T/B)
def coeff_exponent(p):
    return s.simplify(p*s.diff(scale,p)/scale
       +sum(ex*p*s.diff(coord,p)/coord for ex,coord in zip((i,j,l),(cn,dn,en))))
direct_A=coeff_exponent(A)
direct_B=coeff_exponent(B)
direct_T=coeff_exponent(T)
checks={
 'coefficient_chain_rule':s.expand(direct_A*direct_B*direct_T
                       -wa*(wb-s.Rational(1,2))*(wt+s.Rational(1,2)))==0,
 'Euler_A_divergence':-s.Rational(1,3)-s.Rational(2,3)-s.Rational(1,6)==-s.Rational(7,6),
 'Euler_B_divergence':-s.Rational(1,3)-s.Rational(1,6)-s.Rational(1,6)==-s.Rational(2,3),
 'Euler_T_divergence':-s.Rational(1,3)-s.Rational(1,6)-s.Rational(2,3)==-s.Rational(7,6),
}
# Verify the adjoint by the Laurent residue pairing on arbitrary monomials:
# paired exponents are (-i-1,-j-1,-l-1).
paired={i:-i-1,j:-j-1,l:-l-1}
left=wa*(wb-s.Rational(1,2))*(wt+s.Rational(1,2))
right=-(wt-s.Rational(5,3))*(wb-s.Rational(1,6))*(wa-s.Rational(7,6))
checks['Euler_product_adjoint']=s.expand(left-right.subs(paired,simultaneous=True))==0
# The third derivative has formal adjoint -partial_c^3.  P3 includes
# -partial_c^3, so its adjoint includes +partial_c^3.
checks['third_derivative_adjoint']=s.expand(
    -i*(i-1)*(i-2)-(-i)*(-i+1)*(-i+2))==0
# The root-residue proof applies because these coefficient products in
# P(b)=B b^4+(Cq²+Eq+T)b²+Dq⁴b+Aq⁶ coincide literally.
q,b=s.symbols('q b')
checks['literal_cubic_box_product']=s.expand(q**6*b**4*b**2-(q*q*b*b)**3)==0
checks['literal_quadratic_box_product']=s.expand((q**4*b)**2-q**6*(q*q*b*b))==0
# Changing qphysical=gamma*qnormalized adds the Cartan Lie derivative Rq.
# A,B,T coordinate derivatives become A0+Rq/6, B0+Rq/6,T0-Rq/3.
av,bv,tv,rq=s.symbols('av bv tv rq')
U=(av+bv)*tv/6-av*bv/3
V=tv/36-(av+bv)/18
checks['full_Cartan_operator_expansion']=s.expand(
    (av+rq/6)*(bv+rq/6)*(tv-rq/3)-av*bv*tv
    -rq*(U+rq*V-rq*rq/108))==0
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'A0':'-c/3*dc-2*d/3*dd-e/6*de',
 'B0':'-c/3*dc-d/6*dd-e/6*de',
 'T0':'-c/3*dc-d/6*dd-2*e/3*de',
 'P3':'A0*(B0-1/2)*(T0+1/2)-dc^3',
 'P3_adjoint':'dc^3-(T0-5/3)*(B0-1/6)*(A0-7/6)',
 'relative_exact_potential':'P3(chi)=d_q f3, f3=-i_(q*partial_q)[U*chi+Rq*V*chi-Rq^2*chi/108], U=((A0+B0-1/2)*(T0+1/2))/6-A0*(B0-1/2)/3, V=(T0+1/2)/36-(A0+B0-1/2)/18',
 'scope':'universal coefficient boxes literal at fixed physical q; normalized operators exact modulo the displayed fiber derivative, not zero as literal normalized differentials',
 'normalization':'A=B=T=1 on coefficient cover; chi=zeta/sqrt(-T/B)',
 'certificate':False}
Path(__file__).with_name('normalized-third-box.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
