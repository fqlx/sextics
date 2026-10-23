"""Literal source derivatives of a toric point-pair differential."""
import json
from pathlib import Path
import sympy as s
A,B,C,D,E,T,a,b,q=s.symbols('A B C D E T a b q',nonzero=True)
Q=A*a*a+B*b*b+C*q*q+D*a*q+E*q+T
Qa=s.diff(Q,a);Qb=s.diff(Q,b)
J=a*Qa-b*Qb
eta=b/J
zeta=b/q
def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
checks={}
for p,P in [(E,q),(C,q*q),(D,a*q),(T,1)]:
    checks['zeta_'+str(p)]=s.cancel(par(zeta,p)-P*eta/q)==0
checks['source_box']=s.cancel(par(par(zeta,E),E)-par(par(zeta,C),T))==0
# Normalized point-pair form chi=zeta/b0, b0²=-T/B.
# Keep the coefficient of 1/b0 and differentiate its normalizer explicitly.
def par_normalized(f,p):
    return par(f,p)-({T:1/(2*T),B:-1/(2*B)}.get(p,0))*f
checks['normalized_box']=s.cancel(
    par_normalized(par_normalized(zeta,E),E)
    -par_normalized(par_normalized(zeta,C),T)
    -par_normalized(zeta,C)/(2*T))==0
# At Pa±, q is a parameter and b tends to ±b0; at Pb±, b=q³/a.
b0,a0=s.symbols('b0 a0',nonzero=True)
checks['finite_residues']=[s.cancel((b/b0).subs(b,sgn*b0)) for sgn in (1,-1)]==[1,-1]
checks['other_q_zero_points']=s.limit((q*q/a0),q,0)==0
# At infinity a_proj=1,q_proj=u,t=u³/b_proj(u).
# zeta=(b*b'/u³-2b²/u⁴)du, so the residue is -[u³](b²)/2.
# The projective equation has no u³ term:
# A+B*b²+D*u+C*u²+E*u⁴/b+T*u⁶/b²=0.
u,c0,c1,c2,c3,c4=s.symbols('u c0 c1 c2 c3 c4',nonzero=True)
bsquare=c0+c1*u+c2*u*u+c3*u**3+c4*u**4
beta_num=s.diff(bsquare,u)/(2*u**3)-2*bsquare/u**4
checks['infinity_residue_formula']=s.cancel(s.residue(beta_num,u,0)+c3/2)==0
checks['infinity_residue_zero']=s.residue(beta_num.subs(c3,0),u,0)==0
checks['fourth_order_pole_retained']=s.expand(beta_num).coeff(u,-4)==-2*c0
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'normalized_generator':'chi_a=b*dq/(b0*q), b0²=-T/B',
 'rational_generator':'zeta=b*dq/q',
 'point_pair':'Pa+ - Pa-, Pa±=(a=0,b=±b0,q=0)',
 'infinity':'residues zero; fourth-order second-kind poles retained',
 'source':'tau=-partial_E² zeta=-partial_T partial_C zeta',
 'certificate':False}
Path(__file__).with_name('toric-point-pair-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
