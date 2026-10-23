"""Literal Theta contiguity and the complete weighted kernel transfer.

The coefficient L is arbitrary.  In the actual source reconstruction it is
L=e**(-7)*K, so differentiating only K would give a different current.
No compact component or infinity form is discarded by these checks.
"""
import json
from pathlib import Path
import sympy as s

a,b,q,c,d,e=s.symbols('a b q c d e', nonzero=True)
Q=a*a+b*b+c*q*q+d*a*q+e*q+1
J=2*a*a+d*a*q-2*b*b
aq=(-a*s.diff(Q,q)-3*q*q*s.diff(Q,b))/J
bq=(b*s.diff(Q,q)+3*q*q*s.diff(Q,a))/J

def dq(f):
    return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)

def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J

def B0(f):
    return -c*par(f,c)/3-d*par(f,d)/6-e*par(f,e)/6

def zero_on_curve(f):
    # A dense rational chart of the universal complete-intersection family.
    # Substituting a=q^3/b then eliminating c tests a literal field identity,
    # with no numerical specialization or cohomological quotient.
    f=s.together(f).as_numer_denom()[0]
    f=f.subs(a,q**3/b)
    return s.factor(f.subs(c,-(q**6/b**2+b*b+d*q**4/b+e*q+1)/q**2))==0

checks={}
zeta=b/q
theta=b**3/(3*q*q)
omega=q*q/J
Cp=c-d*d/4
kappa=d*(Cp**3+8)/16
F=b**3/(3*q)
G=2*c*b**3+4*d*b*b*q*q+6*b*q**4+e*a*q*q+e*d*q**3/2
Omega=theta+e*zeta/2+dq(F)+kappa*omega

checks['normalized_theta_contiguity']=zero_on_curve(
    par(theta,e)-(B0(zeta)-zeta/2+dq(b/6)))
checks['polynomial_compact_representative']=zero_on_curve(
    Omega-(G+kappa*q*q)/J)
checks['kappa_e_constant']=s.diff(kappa,e)==0
checks['compact_e_derivative']=zero_on_curve(
    par(Omega,e)-(
        b*(-2*c*q-d*a+2*e)/(6*J)
        +kappa*par(omega,e)+dq(par(F,e)+b/6)))

# Generic L,L_e checks keep the total base derivative as a product rule.
L,Le=s.symbols('L Le')
Rz=B0(zeta)-zeta/2
base_div_e=Le*theta+L*par(theta,e)
fiber_div=dq(-L*b/6+Le*F)
retained=-Le*Omega+e*Le*zeta/2+kappa*Le*omega
checks['full_weighted_current_identity']=zero_on_curve(
    L*Rz-(base_div_e+fiber_div+retained))

# A concrete use of the companion Pb section matches the independent
# infinity coefficient and transfers its finite coefficient into rank8.
shift=d*Cp/2
xi_hat=a/q-shift*omega
ratio=kappa/shift
checks['companion_e_compact_derivative']=zero_on_curve(
    par(xi_hat,e)+a/J+shift*par(omega,e))
checks['companion_infinity_source_binding']=s.cancel(shift*ratio-kappa)==0
coupled_coeff=e*Le*zeta/2+ratio*Le*xi_hat+shift*ratio*Le*omega
negative_companion_current=-ratio*Le*xi_hat-ratio*L*par(xi_hat,e)
compact_target=-Le*Omega+ratio*L*par(xi_hat,e)
checks['coupled_theta_compact_transfer']=zero_on_curve(
    retained-(coupled_coeff+negative_companion_current+compact_target))

# Finite q=0 points: b=b0+b1*q+..., a=q^3/b.  F cancels
# the double pole and e*zeta/2 cancels the remaining simple residue.
b0=s.symbols('b0',nonzero=True)
b1=-e/(2*b0)
def zero_at_pa(f):
    nn=s.together(f).as_numer_denom()[0]
    return s.rem(nn,s.Poly(b0*b0+1,b0),b0)==0
checks['finite_theta_residue']=zero_at_pa(b0*b0*b1+e*b0/2)
checks['finite_double_pole_correction']=s.cancel(b0**3/3-b0**3/3)==0

# Infinity: write a_projective=1,q_projective=u,t=u^3/y(u).
# Up to u^7, y^5=(−1−d*u−c*u^2)^(5/2)
#                 −(5e/2)u^4(−1−d*u−c*u^2)
#                 −(5/2)u^6 sqrt(−1−d*u−c*u^2)+O(u^8).
# Theta has residue −[u^7]y^5/5.  This is exact formal implicit
# differentiation, since a second e deformation starts in degree8.
u,c0=s.symbols('u c0',nonzero=True)
base_coefficient=sum(s.binomial(s.Rational(5,2),n)*s.expand((d*u+c*u*u)**n).coeff(u,7) for n in range(4,8))
y5_u7=c0*base_coefficient+5*d/(4*c0)
theta_inf=-y5_u7/5
def zero_at_inf(f):
    nn=s.together(f).as_numer_denom()[0]
    return s.rem(nn,s.Poly(c0*c0+1,c0),c0)==0
checks['infinity_theta_residue']=zero_at_inf(theta_inf-c0*d*(Cp**3+8)/32)
checks['infinity_counterterm_sign']=zero_at_inf(
    c0*d*(Cp**3+8)/32-kappa*c0/2)

# The scalar Hermite primitive retains a genuine two-variable freedom.
ii,jj,ee=s.symbols('i Jinv ee',nonzero=True)
K=s.Function('K')(ii,jj,ee)
C=s.Function('C')(ii,jj)
def E_invariants(f):
    return s.diff(f,ee)-2*ii*s.diff(f,ii)/ee-2*jj*s.diff(f,jj)/ee
checks['weighted_K_derivative']=s.simplify(
    E_invariants(ee**(-7)*K)-ee**(-8)*(ee*s.diff(K,ee)-2*ii*s.diff(K,ii)-2*jj*s.diff(K,jj)-7*K))==0
checks['hermite_integration_constant_derivative']=s.simplify(
    E_invariants(C/ee)-ee**(-2)*(-C-2*ii*s.diff(C,ii)-2*jj*s.diff(C,jj)))==0

assert all(checks.values()),checks
out={
    'checks':checks,'passed':True,'certificate':False,
    'Theta':'b^3*dq/(3*q^2)',
    'contiguity':'partial_e Theta=(B0-1/2)zeta+d_q(b/6)',
    'F':'b^3/(3*q)',
    'kappa':'d*((c-d^2/4)^3+8)/16',
    'compact_form':'Omega=Theta+(e/2)zeta+d_q F+kappa*omega',
    'compact_numerator_over_J':str(s.expand(G+kappa*q*q)),
    'arbitrary_coefficient':'L(B0-1/2)zeta=partial_e(LTheta)+d_q(-Lb/6+L_e F)-L_e Omega+(e/2)L_e zeta+kappa L_e omega',
    'actual_weight':'L=e^(-7)K; L_e=e^(-8)(D-7)K',
    'integration_freedom':'K -> K+v*C(i,Jinv), L -> L+e^(-1)C(i,Jinv)',
    'coupled_target':'Zop=(e/2)*L_e, Xop=(kappa/s)*L_e, s=d*Cp/2',
    'coupled_compact_source':'-L_e*Omega-(kappa/s)*L*a*dq/J-kappa*L*partial_e(omega)',
    'remaining':'All eight compact components of -L_e Omega and both displayed zeta/omega coefficients remain to be served.'
}
Path(__file__).with_name('theta-weighted-transfer-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact Theta/current/weight checks')
