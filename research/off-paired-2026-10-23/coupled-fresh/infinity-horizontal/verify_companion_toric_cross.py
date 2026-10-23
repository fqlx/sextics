"""Companion Pb pair, its actual source, and its retained infinity correction."""
import json
from pathlib import Path
import sympy as s
A,B,C,D,E,T,a,b,q=s.symbols('A B C D E T a b q',nonzero=True)
Cp=C-D*D/(4*A)
Q=A*a*a+B*b*b+C*q*q+D*a*q+E*q+T
Qa=s.diff(Q,a);Qb=s.diff(Q,b);Qq=s.diff(Q,q)
J=a*Qa-b*Qb
aq=(-a*Qq-3*q*q*Qb)/J
bq=(b*Qq+3*q*q*Qa)/J
def dq(f):return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)
def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
def reduce_polynomial(poly):
    # Explicit ideal reductions ab=q³ and Aa²=−Bb²−Cq²−Daq−Eq−T.
    terms=list(s.Poly(s.expand(poly),a,b,q).terms());out={}
    while terms:
        (ia,ib,iq),co=terms.pop()
        mm=min(ia,ib)
        if mm:
            terms.append(((ia-mm,ib-mm,iq+3*mm),co));continue
        if ia>=2:
            for (ja,jb,jq),cc in s.Poly(-B*b*b-C*q*q-D*a*q-E*q-T,a,b,q).terms():
                terms.append(((ia-2+ja,ib+jb,iq+jq),co*cc/A))
            continue
        out[(ia,ib,iq)]=out.get((ia,ib,iq),0)+co
    return s.factor(sum(s.factor(co)*a**ia*b**ib*q**iq for (ia,ib,iq),co in out.items()))
def zero_on_curve(expr):
    num=s.together(expr).as_numer_denom()[0]
    reduced=reduce_polynomial(num)
    if reduced==0:return True
    # The two displayed reductions are not a full Groebner basis.  The
    # remaining S relation is resolved independently on the dense chart a≠0.
    return s.factor(num.subs(b,q**3/a).subs(
        T,-A*a*a-B*q**6/a**2-C*q*q-D*a*q-E*q))==0

xi=a/q
xi2=1/b
eta=b/J
r=(Cp-E*E/(4*T))/(2*T)
shift=D*Cp/(2*A)
F=a/(2*q*q)+(D*a*a+E*a)/(4*T*q)
checks={
 'literal_eta_a':s.cancel(par(xi,E)+a/J)==0,
 'literal_eta_b_cross':s.cancel(par(xi2,B)+eta)==0,
 'norm_fiber_shift':s.factor((xi2-xi/q**2).subs(b,q**3/a))==0,
 'eta_contiguity_CE':s.cancel(par(eta,C)-q*par(eta,E))==0,
}
# Construct the polynomial/J representative of the corrected compact form.
raw_numerator4Tq2=(-a*Qq-6*B*b*q*q)*(2*T+(2*D*a+E)*q) \
    -J*(D*a*a+E*a)-4*T*r*a*q*J
G=s.factor(reduce_polynomial(raw_numerator4Tq2)/(4*T*q*q)+r*shift*q*q)
psi=xi2+dq(F)-r*xi+r*shift*q*q/J
checks['compact_polynomial_representative']=zero_on_curve(psi-G/J)
# This is the direct source cross relation, including the infinity companion.
# It follows literally because r_B=shift_B=0 and parameter/fiber lifts commute.
checks['r_B_constant']=s.diff(r,B)==0
checks['shift_B_constant']=s.diff(shift,B)==0
checks['companion_B_derivative']=zero_on_curve(par(xi,B)+q*q*eta)

# Pb expansion a=a_s+a1 q+a2 q².  B b² first enters at q^6.
a_s=s.symbols('a_s',nonzero=True)
a1=-D/(2*A)-E/(2*A*a_s)
a2=r*a_s
def on_pb(expr):
    nn,dd=s.fraction(s.cancel(expr))
    return s.rem(nn,s.Poly(a_s*a_s+T/A,a_s),a_s)==0
checks['Pb_first_jet']=on_pb(2*A*a_s*a1+D*a_s+E)
checks['Pb_residue']=on_pb(A*(a1*a1+2*a_s*a2)+D*a1+C)
checks['Pb_double_pole_cancellation']=on_pb(a1/2-(D*a_s*a_s+E*a_s)/(4*T))
checks['Pa_potential_regular']=s.limit(F.subs(a,q**3/b),q,0)==0

# In a_projective=1,q_projective=u,t=u³/b(u), xi=(b'/u³−2b/u⁴)du.
# Q fixes b(u)^2 through degree3; b(u) itself has a nonzero degree3 term.
c0=s.symbols('c0',nonzero=True)
b1=-D/(2*B*c0)
b2=-C/(2*B*c0)-b1*b1/(2*c0)
b3=-b1*b2/c0
cinf=D*Cp/(4*A*B*c0)
def on_infinity(expr):
    nn,dd=s.fraction(s.cancel(expr))
    return s.rem(nn,s.Poly(c0*c0+A/B,c0),c0)==0
checks['companion_infinity_residue']=on_infinity(b3-cinf)
checks['rational_infinity_correction']=on_infinity(cinf*(-2*A/c0)-shift)
checks['corrected_compact_residue']=on_infinity(-r*cinf+r*shift*(-c0/(2*A)))
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'xi':'a*dq/q; normalized by a0²=-T/A for Pb± residues±1',
 'xi2':'dq/b=a*dq/q³',
 'source':'tau=partial_E partial_B xi2; partial_B xi2=-eta_b literally',
 'r':'(Cp-E²/(4T))/(2T)',
 'F':'a/(2q²)+(D*a²+E*a)/(4T*q)',
 'infinity_residue_xi':'D*Cp/(4*A*B*c0), c0²=-A/B; generally NONZERO',
 'rational_shift':'s=D*Cp/(2A), xi_hat=xi-s*q²dq/J',
 'compact_form':'psi_hat=xi2+d_q F-r*xi+r*s*q²dq/J',
 'compact_numerator_over_J':str(G),
 'cross_source':'partial_B psi_hat=(r*q²-1)*eta_b+d_q(partial_B F)+r*s*partial_B(q²dq/J)',
 'pole_scope':'psi_hat has only infinity poles of order at most5, all residues0',
 'certificate':False}
Path(__file__).with_name('companion-toric-cross.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='compact_numerator_over_J'}))
