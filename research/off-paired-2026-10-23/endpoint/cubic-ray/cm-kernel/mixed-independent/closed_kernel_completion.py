"""A closed-residue completion and its exact pure-component reduction.

This is an actual partial current.  Its attempted standalone closure lies
in the already excluded pure-component scope; it is not a new exclusion.
"""
import json
from pathlib import Path
import sympy as S

c,h,H,B,bh,E=S.symbols('c h H B bh E',nonzero=True)
C=c**6
Hc=-6*(H-1-h**6)/c
Bc=B/c-2*h*E/c**2
bhc=bh/c-2*E/c**2
def partial_c(value):
    return S.diff(value,c)+Hc*S.diff(value,H)+Bc*S.diff(value,B)+bhc*S.diff(value,bh)
def partial_h(value):
    return S.diff(value,h)+6*h**5*S.diff(value,H)+bh*S.diff(value,B)
J=H*bh-4*B*h**5
kap=B**3/(C*H**2)
checks=[]
def check(name,value):
    result=S.cancel(value)
    assert result==0,(name,S.factor(result))
    checks.append(name)

Jc=H*Bc-2*B*H/c-S.Rational(2,3)*B*Hc
r=Jc/J
def U(value):return partial_c(value)-r*partial_h(value)
ell=S.Rational(2,3)*U(H)/H-U(J)/J
check('physical-lambda-h',partial_h(kap)/kap-3*J/(B*H))
check('complete-kappa-horizontal-lift',U(kap))
check('lift-ratio',r-partial_c(kap)/partial_h(kap))

# The normalized trace of F*dP, F=4*c*y*m, gives W times this
# explicitly rational base vector.  All source derivatives remain.
Dc=c/(C*H)
Dh=-c*r/(C*H)
div=partial_c(Dc)+4*Dc/c+partial_h(Dh)
check('actual-partial-current-divergence',div-(1+c*ell)/(C*H))
check('no-V-row',Dc*partial_c(kap)+Dh*partial_h(kap))
check('mixed-current-normalization',
      Dc-c**5*B/(3*C*J)*partial_h(kap)/kap/c**4)

# Polynomial cubic reduction checks the coefficient entering the trace.
p,H0,B0,C0,J0,a0=S.symbols('p H0 B0 C0 J0 a0',nonzero=True)
f=C0*p**3+B0*p+H0;g=B0+3*C0*p**2
s=-64*H0/(C0*p**3)
def mod_f(value):
    n,d=S.fraction(S.cancel(value))
    return S.rem(S.Poly(n,p),S.Poly(f,p)).as_expr()/d
m0=-c**4*p**2*(s-64)/(2*a0*(s+128)**2*J0)
check('normalized-B-over-g',mod_f((s-64)/(s+128)-B0/g))
check('kernel-completion-trace-W-coefficient',mod_f(
    S.Rational(2,3)*c*m0*s*(s-64)/(s+128)
    -c**5*B0/(3*a0*C0*J0)*(C0*H0*B0*p/g**3)))

data={
 'status':'Actual closed-residue CM completion with retained derivative; its standalone closure reduces to the already excluded pure-W scope',
 'constant_scope':'fixed characteristic-zero k; k=C for full contract',
 'checks':checks,'check_count':len(checks),
 'physical_constants':'A=T*V/2,D=V/3,E=T*V^2/(2Y2), with E2 point fixed for partial_c/partial_h',
 'current_before_trace':'J_F=Pminus wedge d(4*c*y*m) wedge eta2',
 'closed_graph_residue':'Res(Pminus)*d(4*c*y*m)|graph wedge eta2',
 'exact_current_identity':'J_F=4*c*y*m*dPminus wedge eta2-d(4*c*y*m*Pminus wedge eta2)',
 'after_normalized_trace_mod_exact':'W*c^5*B/(3*a_scale*C*J) eta1 wedge dlog(kappa) wedge eta2',
 'base_vector':{'c':str(Dc),'h':str(Dh),'E1':'0','E2':'0'},
 'horizontal_lift':str(r),
 'density_derivative_ratio':'ell=(2/3)*U_c(H)/H-U_c(J)/J, U_c=partial_c-r*partial_h',
 'source':'div(W*D)=(1+c*ell)*R',
 'remaining':'c*ell*R',
 'scope':'Because D(log(kappa))=0 and only W remains modulo an exact current, a complete primitive in this closed-dF kernel family would be a pure-W solution. The previously audited pure-component obstruction applies. A genuine new mixed correction must retain a second independent component or residue class.',
}
Path(__file__).with_name('closed-kernel-completion-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact mixed-completion and scope identities')
