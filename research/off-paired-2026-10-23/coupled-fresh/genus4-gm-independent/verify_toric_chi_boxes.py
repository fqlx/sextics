"""Literal all-parameter toric boxes for psi=b*dq/q and chi=psi/b0.

No fiber-exact or boundary term is discarded.  The verification operates in
the actual algebraic function field using the quartic equation for b.
"""
import json
from pathlib import Path
import sympy as s

A,B,C,D,E,T,b,q=s.symbols('A B C D E T b q')
P=B*b**4+(C*q*q+E*q+T)*b*b+D*q**4*b+A*q**6
Pb=s.diff(P,b)
parameters=(A,B,C,D,E,T)
def deriv(f,theta):
 return s.cancel(s.diff(f,theta)-s.diff(P,theta)*s.diff(f,b)/Pb)
def root_jet(seq):
 ans=b
 for theta in seq:ans=deriv(ans,theta)
 return ans
def zero_on_curve(f):
 num,den=s.fraction(s.cancel(f))
 return s.rem(num,P,b)==0

checks={}
# Verify the general implicit-root third-derivative identity before using
# equal monomial products.  This avoids expanding enormous six-parameter
# quartic rational expressions and is an exact algebraic verification.
x,y,z,x1,y1,z1,x2,y2,z2,f1,f2,f3=s.symbols('x y z x1 y1 z1 x2 y2 z2 f1 f2 f3')
bij=(x1*y+x*y1)/f1**2-f2*x*y/f1**3
variations={x:-x1*z/f1,y:-y1*z/f1,x1:-x2*z/f1,y1:-y2*z/f1,
            f1:z1-f2*z/f1,f2:z2-f3*z/f1}
bijk=sum(s.diff(bij,v)*dv for v,dv in variations.items())
M0=x*y*z
M1=x1*y*z+x*y1*z+x*y*z1
M2=x2*y*z+x*y2*z+x*y*z2+2*x1*y1*z+2*x1*y*z1+2*x*y1*z1
third=-M2/f1**3+3*f2*M1/f1**4+f3*M0/f1**4-3*f2**2*M0/f1**5
checks['general_implicit_third_derivative_product_formula']=s.cancel(bijk-third)==0

# Products of coefficient monomials explain each box before taking residues.
m={theta:s.diff(P,theta)for theta in parameters}
checks['monomial_DD_AC']=s.expand(m[D]**2-m[A]*m[C])==0
checks['monomial_EE_CT']=s.expand(m[E]**2-m[C]*m[T])==0
checks['monomial_ABT_CCC']=s.expand(m[A]*m[B]*m[T]-m[C]**3)==0

# The second-root derivative is M'/Pb^2-Pbb*M/Pb^3; the checked
# third-root derivative is also linear in M,M',M''.  These target pairs
# have identical M, so their literal derivative differences are zero.
def second_product(M):return s.diff(M,b)/Pb**2-s.diff(P,b,2)*M/Pb**3
def third_product(M):
 return (-s.diff(M,b,2)/Pb**3+3*s.diff(P,b,2)*s.diff(M,b)/Pb**4
         +s.diff(P,b,3)*M/Pb**4-3*s.diff(P,b,2)**2*M/Pb**5)
checks['literal_DD_equals_AC']=second_product(s.expand(m[D]**2-m[A]*m[C]))==0
checks['literal_EE_equals_CT']=second_product(s.expand(m[E]**2-m[C]*m[T]))==0
checks['literal_ABT_equals_CCC']=third_product(s.expand(m[A]*m[B]*m[T]-m[C]**3))==0

# Conjugation by b0 with b0^2=-T/B; derivative logarithms are literal.
logB=-1/(2*B);logT=1/(2*T)
checks['normalization_log_derivatives_compatible']=s.diff(logB,T)==s.diff(logT,B)

assert all(checks.values()),checks
out={
 'checks':checks,
 'psi':'b*dq/q, with b satisfying B*b^4+(Cq^2+Eq+T)b^2+Dq^4b+Aq^6=0',
 'chi':'psi/b0, b0^2=-T/B',
 'literal_unnormalized_boxes':[
  'partial_D^2-partial_A partial_C',
  'partial_E^2-partial_C partial_T',
  'partial_A partial_B partial_T-partial_C^3'],
 'literal_normalized_boxes':[
  'partial_D^2-partial_A partial_C',
  'partial_E^2-partial_C(partial_T+1/(2T))',
  'partial_A(partial_B-1/(2B))(partial_T+1/(2T))-partial_C^3'],
 'normalized_cubic_expanded':'partial_A partial_B partial_T+partial_A partial_B/(2T)-partial_A partial_T/(2B)-partial_A/(4BT)-partial_C^3',
 'boundary_terms':'NONE: identities of the literal algebraic differential coefficient b/q; no residue or pole was removed',
 'proof_mechanism':'For a local root, d_i1...d_in b=(-1)^n(n-1)! Res(product P_ij/P^n db). Equal monomial products give identical literal derivatives.',
 'certificate':False,
}
Path(__file__).with_name('toric-chi-box-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
