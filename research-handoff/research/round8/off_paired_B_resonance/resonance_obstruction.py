"""Exact s=0,nu=0 leading equation for the generic cyclic scalar route.

The analytic/rational-function valuation proof is in resonance_obstruction.md.
This script independently derives every coefficient from the pinned physical
source and vector field. It does not use a worked-level specialization.
"""
from pathlib import Path
import json,time
import sympy as sp

HERE=Path(__file__).parent
start=time.monotonic()
eta,V,s,nu=sp.symbols('eta V s nu')
c=sp.Rational(5,7)
obj=json.loads(Path('/workspace/research/round8/cyclic_companion/gist/results/original_scalar_input.json').read_text())
Y=[sp.sympify(t)for t in obj['contracted_boundary_reduction']['Y_components']]
Delta=sp.sympify(obj['contracted_boundary_reduction']['Delta0'])
T=sp.sympify(obj['T']);R=sp.sympify(obj['contracted_boundary_reduction']['Rnum0'])
k=1+V**6+s*s
q=3*k-c*V*V*s*(eta+1)*(eta*V*V+1)
M=3*k/q
variables=(eta,V,s)
def delta(f):return sp.cancel(sum(Y[i]*sp.diff(f,z)for i,z in enumerate(variables))/(q*Delta))
Delta_s0=sp.factor(Delta.subs(s,0))
q_s0=3*(1+V**6)
vel=[sp.factor(f.subs(s,0)/(q_s0*Delta_s0))for f in Y[:2]]
mu=sp.factor(sp.diff(Y[2],s).subs(s,0)/(q_s0*Delta_s0))
assert Y[2].subs(s,0)==0
assert sp.factor(vel[0]+sp.Rational(9,5)*(eta+1)*(9*eta+14))==0
AA=sp.sympify(obj['connection_numerator_A'])
assert AA.subs(s,0)==0
# Raw Delta=s*Delta0 and a_kappa=AA/(q^2*Delta), hence this
# independently checks the charge limit against the pinned numerator.
charge_s0=sp.factor(sp.diff(AA,s).subs(s,0)/(q_s0*q_s0*Delta_s0))
assert sp.cancel(charge_s0-mu/3)==0

# M=1 along the invariant divisor, so its tangential derivative vanishes.
# Verify this from the explicit boundary tangent vector, not a charge guess.
assert sp.cancel(M.subs(s,0)-1)==0
assert sum(vel[i]*sp.diff(M.subs(s,0),z)for i,z in enumerate([eta,V]))==0
# Consequently a_kappa=(delta log s-2 delta log M)/3 tends to mu/3.
E=eta+1
hh=eta*V*V+1
xx=3*V**3*s*E**3/q
rx=(3*c*eta*k-c*c*V*s*hh*hh)/(E*q)
L=(27*k*k*(1+eta**6*s*s)-9*c*c*eta*V*V*s*k*hh+2*c**3*V**3*s*s*hh**3)/(3*q*q)
assert sp.cancel(xx.subs(s,0))==0
assert sp.cancel(L.subs(s,0)-1)==0
A0=(4*c*c*xx-5*xx*rx)/3+27
C0=(100*(xx*rx)**2+20*c*c*xx*(xx*rx)-54*xx*rx+270*xx*L+10*c**4*xx**2+324*c*c*xx+1458)/9
assert sp.cancel(A0.subs(s,0))==27
assert sp.cancel(C0.subs(s,0))==162
rhs_s=sp.factor(-sp.Rational(3,5)*T.subs(s,0)*R.subs(s,0)/Delta_s0**3)
assert sp.factor(rhs_s-sp.Rational(55566,125)*(2*V**6*eta-V**4+eta)/(V*(V*V*eta-1)**3))==0

eta_sub=(nu-14)/9
delta_nu=sp.factor(9*vel[0].subs(eta,eta_sub))
assert sp.cancel(delta_nu/nu).subs(nu,0)==9
C=sp.cancel(nu*vel[1].subs(eta,eta_sub)).subs(nu,0)
C=sp.factor(C)
C_expected=-sp.Rational(475,3)*V*V/(14*V*V+9)
assert sp.cancel(C-C_expected)==0
mu_lead=sp.cancel(nu*mu.subs(eta,eta_sub)).subs(nu,0)
assert sp.cancel(mu_lead-C*3*(V**6-1)/(V*(1+V**6)))==0
R0=sp.factor(rhs_s.subs(eta,-sp.Rational(14,9)))
R0_expected=sp.Rational(4500846,125)*(28*V**6+9*V**4+14)/(V*(14*V*V+9)**3)
assert sp.cancel(R0-R0_expected)==0
# The requested rational gauge u_old=g*u_new is a unit at this second
# place: g_s0=1/(3*c*eta), with inverse value -10/3 at eta=-14/9.
gauge_inverse_at_nu0=3*c*(-sp.Rational(14,9))
assert gauge_inverse_at_nu0==-sp.Rational(10,3)
assert sp.cancel((vel[0]/eta).subs(eta,eta_sub)).subs(nu,0)==0
assert sp.limit(V*R0,V,0)!=0
assert sp.limit(V*R0,V,sp.oo)!=0
assert sp.gcd(28*V**6+9*V**4+14,14*V**2+9)==1
assert sp.gcd(28*V**6+9*V**4+14,1+V**6)==1

# Direct operator coefficient check on algebraically independent jets.
# u=s^n w -> (delta-a_kappa)u=s^n[delta0+(n-1/3)mu]w.
n,m=sp.symbols('n m',integer=True)
assert sp.expand(-(n-sp.Rational(1,3))*3).subs(n,-m)==3*m+1
# At nu=0, delta_nu=O(nu), so its contribution is one order less singular
# than delta_V=C/nu+O(1). This derives T_a, independently of nu order l.
a,j=sp.symbols('a j')
rr=a*(V**6-1)/(V*(1+V**6))
aa=sp.factor(C*C)
bb=sp.factor(C*sp.diff(C,V)-2*C*C*rr)
cc=sp.factor(C*C*(rr*rr-sp.diff(rr,V))-C*sp.diff(C,V)*rr)
# Exact indicial residue at every root of K=1+V^6.
K=1+V**6
residue_numerator=sp.cancel(a*(V**6-1)/(V*sp.diff(K,V))-a/3)
assert sp.rem(sp.fraction(residue_numerator)[0],K,V)==0
assert sp.gcd(14*V*V+9,K)==1

# At 0 and infinity these scaled limits give the reported indicial factors.
c_zero=sp.limit(C/V**2,V,0)
c_inf=sp.limit(C,V,sp.oo)
ind_zero=sp.expand(aa*j*(j-1)/V**4+bb*j/V**3+cc/V**2)
assert sp.factor(sp.limit(ind_zero,V,0)/c_zero**2)==(a+j)*(a+j+1)
ind_inf=aa*j*(j-1)+bb*j*V+cc*V**2
assert sp.expand(sp.limit(ind_inf,V,sp.oo)/c_inf**2-(j-a)*(j-a-1))==0

report={
 'field':'QQ(eta,V,s); c=5/7; no fixed invariant level',
 'delta_eta_s0':str(vel[0]),'delta_V_s0':str(vel[1]),'mu_delta_s_over_s':str(mu),
 'M_s0':1,'a_kappa_s0':'mu/3','A0_s0':27,'C0_s0':162,
 'source_times_s':str(rhs_s),
 'leading_s_operator':'For u=s^n*w: [(delta0+(n-1/3)*mu)^2-27*(delta0+(n-1/3)*mu)+162]w',
 'nu':'9eta+14','delta_nu':str(delta_nu),'delta_V_leading':str(C)+'/nu',
 'mu_leading':str(sp.factor(mu_lead))+'/nu',
 'T_a':'C(V)*(d/dV-a*(V^6-1)/(V*(1+V^6)))',
 'a_for_u_s_power_minus_m':'3m+1',
 'T_a_squared_coefficients':list(map(str,[aa,bb,cc])),
 'required_equation':'For u=s^-1*w, w=nu^2*f(V)+higher nu order and T_4^2*f=R0',
 'R0':str(R0),
 'gauged_version':'g is a unit here, g^-1|nu0=-10/3; the gauged T_4 is the same and its RHS is (-10/3)*R0. The additional charge delta(eta)/eta is O(nu).',
 'indicial_data':{
  'K_roots':'(j-a/3)*(j-a/3-1); for a=4 roots 4/3,7/3',
  'V_zero':'(j+a)*(j+a+1); for a=4 valuations -4,-5',
  'V_infinity_growth':'(j-a)*(j-a-1); for a=4 growth degrees 4,5',
  'roots_14V2plus9':'j*(j-2), with RHS pole order3 and operator exponent shift -4',
 },
 'conclusion_scope':'The proof excludes a rational solution of this generic three-variable charged scalar route. It does not exclude a scalar solution on a special invariant level or an unrestricted off-paired/cyclic certificate outside this sufficient reduction.',
 'seconds':round(time.monotonic()-start,3),
}
(HERE/'resonance_obstruction.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
