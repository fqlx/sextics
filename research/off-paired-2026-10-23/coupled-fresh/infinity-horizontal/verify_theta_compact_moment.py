"""Exact source transfer and compact correction of the b^3 moment."""
from pathlib import Path
import json
import sympy as s
A,B,C,D,E,T,a,b,q=s.symbols('A B C D E T a b q',nonzero=True)
Q=A*a*a+B*b*b+C*q*q+D*a*q+E*q+T
J=a*s.diff(Q,a)-b*s.diff(Q,b)
def parU(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
checks={'universal_source_transfer':s.cancel(parU(b**3/(3*q*q),E)-parU(b/q,B))==0}

c,d,e=s.symbols('c d e',nonzero=True)
Q=a*a+b*b+c*q*q+d*a*q+e*q+1
J=2*a*a+d*a*q-2*b*b
Qa=s.diff(Q,a);Qb=s.diff(Q,b);Qq=s.diff(Q,q)
aq=(-a*Qq-3*q*q*Qb)/J;bq=(b*Qq+3*q*q*Qa)/J
def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
def dq(f):return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)
def B0(f):return -c*par(f,c)/3-d*par(f,d)/6-e*par(f,e)/6
def zero_curve(f):
    num=s.together(f).as_numer_denom()[0]
    return s.factor(num.subs(b,q**3/a).subs(c,(-a*a-q**6/a**2-d*a*q-e*q-1)/q**2))==0
zeta=b/q;theta=b**3/(3*q*q)
F=b**3/(3*q);F_low=-b/(3*q)
Cp=c-d*d/4
kappa=d*(Cp**3+8)/16
Nroot=2*c*b**3+4*d*b*b*q*q+6*b*q**4+e*a*q*q+e*d*q**3/2
Nlow=-(a*q+c*b+d*q*q)*J/3+2*e*a*q*q/3+e*d*q**3/2+e*c*b*q/3+(e*e-2*c)*b/3-4*d*q*q/3-2*a*q
checks['normalized_source_Cartan']=zero_curve(par(theta,e)-(B0(zeta)-zeta/2)-dq(b/6))
checks['root_polynomial_representative']=zero_curve(theta+e*zeta/2+dq(F)-Nroot/J)
checks['lower_polynomial_representative']=zero_curve(theta+e*zeta/2+dq(F_low)-Nlow/J)
checks['two_representatives_same_class']=zero_curve((Nroot-Nlow)/J-dq(F-F_low))
omega=q*q/J
Omega=(Nroot+kappa*q*q)/J
eta=b/J
checks['compact_derivative_interface']=zero_curve(
    par(Omega,e)-b*(-2*c*q-d*a+2*e)/(6*J)-kappa*par(omega,e)-dq(par(F,e)+b/6))

# Finite Pa expansions: b0²=-1,b1=-e/(2b0); at Pb, b=q³/a.
b0=s.symbols('b0',nonzero=True)
b1=-e/(2*b0)
bfin=b0+b1*q
finite_principal=s.expand(bfin**3/(3*q*q)+e*bfin/(2*q)+s.diff(bfin**3/(3*q),q))
checks['finite_simple_residue_cancellation']=s.cancel(finite_principal.coeff(q,-1).subs(b0*b0,-1))==0
checks['finite_double_pole_cancellation']=s.cancel(finite_principal.coeff(q,-2))==0
checks['other_q_zero_points_regular']=s.limit((theta+e*zeta/2).subs(b,q**3/a),q,0)==0
checks['finite_exact_potential_regular_at_Pb']=s.limit(F.subs(b,q**3/a),q,0)==0

# Independent infinity computation: h=1+d*u+c*u², b_base=c0*sqrt(h).
# Linearized e*u4 and u6 corrections suffice through orderu7; their square
# starts at orderu8.  In b^5 these terms are +(5/2)e*u4*h and
# -(5c0/2)*u6*sqrt(h), respectively.
u,c0=s.symbols('u c0',nonzero=True)
h=1+d*u+c*u*u
coeff_base=s.expand(sum(s.binomial(s.Rational(5,2),n)*(d*u+c*u*u)**n for n in range(8))).coeff(u,7)
checks['base_seventh_coefficient']=s.factor(coeff_base+5*d*Cp**3/32)==0
checks['e_correction_no_residue']=s.expand(s.Rational(5,2)*e*u**4*h).coeff(u,7)==0
coeff_T=-s.Rational(5,2)*c0*(d/2)
checks['T_infinity_correction']=s.cancel(-coeff_T/5-c0*d/4)==0
res_theta=s.factor(-c0*coeff_base/5-coeff_T/5)
checks['full_infinity_residue']=s.factor(res_theta-c0*d*(Cp**3+8)/32)==0
checks['omega_counterterm_sign']=s.factor(res_theta-kappa*c0/2)==0
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'Theta':'b³dq/(3q²)',
 'source_transfer':'partial_E Theta=partial_B zeta literally; normalized partial_e Theta=(B0-1/2)zeta+d_q(b/6)',
 'F_root':str(F),'F_lower':str(F_low),
 'infinity_residue':'c0*d*(Cp³+8)/32,c0²=-1',
 'kappa':str(kappa),
 'compact_root_numerator':str(s.expand(Nroot+kappa*q*q)),
 'compact_lower_numerator':str(s.expand(Nlow+kappa*q*q)),
 'compact_form':'Omega_Theta=Theta+(e/2)zeta+d_qF_root+kappa*q²dq/J',
 'pole_scope':'only infinity poles, of order at most8, all residues0',
 'derivative_interface':'nabla_e Omega_Theta=b*(-2cq-da+2e)dq/(6J)+kappa*nabla_e(omega)+d_q(F_e+b/6)',
 'certificate':False}
Path(__file__).with_name('theta-compact-moment.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({name:val for name,val in out.items()if 'numerator'not in name}))
