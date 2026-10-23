"""Rational trace of the all-D ruling primitive, with its exact shear potential."""
import json
from pathlib import Path
import sympy as s

A,B,Cp,D,E,a,b,q=s.symbols('A B Cp D E a b q', nonzero=True)
delta=D/(2*A)
X=a+delta*q
Y=q+E/(2*Cp)
W=A*X**2+Cp*Y**2
Qa=2*A*X
Qb=2*B*b
Qq=2*A*delta*X+2*Cp*Y
J=a*Qa-b*Qb
aq=(-a*Qq-3*q*q*Qb)/J
bq=(b*Qq+3*q*q*Qa)/J
ash=-a*q*X/J
bsh=b*q*X/J
def dq(f):
    return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)
def shear(f):
    return s.diff(f,D)+ash*s.diff(f,a)+bsh*s.diff(f,b)
def on_cubic(f):
    # The identity is literal after ab=q^3 and does not need a Q reduction.
    return s.factor(s.cancel(f.subs(b,q**3/a)))

psi=A*b*(X-Y*(aq+delta))/W
potential=B*Y*b**3*q/(J*W)
checks={
 'norm_q': s.cancel(b*aq+a*bq-3*q*q)==0,
 'norm_shear':s.cancel(b*ash+a*bsh)==0,
}
# Direct trace of h beta, eliminating rho²=(W+B b²)/B.
rho=s.symbols('rho',nonzero=True)
raw=-A*(X-Y*(aq+delta))/(B*(b+rho))
trace=s.cancel((raw+raw.subs(rho,-rho))/2)
checks['rational_trace']=s.cancel(trace.subs(rho**2,(W+B*b*b)/B)-psi)==0
# A compact polynomial Cartan calculation avoids expanding a third-order
# rational expression.  If P=2A X q*d_delta+2Cp Y*d_e, then
# a_V=-aP/J,b_V=bP/J.  The numerator after combining the J^-2 terms is N.
dd,de=s.symbols('d_delta d_e')
P=2*A*X*q*dd+2*Cp*Y*de
Bq=b*Qq+3*q*q*Qa
N=Bq*X*de+3*q*q*P*Y-Bq*Y*q*dd-b*P*X+b*P*Y*delta
expected=2*W*(-dd*b*q+de*(delta*b+3*q*q))
checks['cartan_translation_polynomial']=s.factor(N-expected)==0
# At dd=1/(2A),de=0 this is exactly the shear source term;
# the product derivative supplies the displayed exact potential.
checks['trace_shear_source']=s.cancel((-A)*expected.subs({dd:1/(2*A),de:0})/(W*J)-b*q/J)==0
trace_potential=s.cancel((
    -Y*b*b*q/(J*(b+rho))-Y*b*b*q/(J*(b-rho))
    )/2).subs(rho**2,(W+B*b*b)/B)
checks['trace_shear_potential']=s.cancel(trace_potential-potential)==0
checks['trace_Y_translation_source']=s.cancel(
    -A*expected.subs({dd:0,de:1/(2*Cp)})/(W*J)
    +A*(delta*b+3*q*q)/(Cp*J))==0
raw_Y_potential=-A*(X*J+2*Cp*a*Y*Y)/(2*B*Cp*J*(b+rho))
trace_Y_potential=s.cancel((raw_Y_potential+raw_Y_potential.subs(rho,-rho))/2)
trace_Y_potential=trace_Y_potential.subs(rho**2,(W+B*b*b)/B)
checks['trace_Y_translation_potential']=s.cancel(
    trace_Y_potential-A*b*(X*J+2*Cp*a*Y*Y)/(2*Cp*J*W))==0
c0=s.symbols('c0',nonzero=True)
checks['rational_infinity_normalization']=s.cancel(
    (3*A*A*E/(B*Cp*c0*c0)).subs(c0*c0,-A/B)+3*A*E/Cp)==0
assert all(checks.values()), checks
out={
 'checks':checks,
 'passed':True,
 'psi':'A*b*(X*dq-Y*dX)/(A*X^2+Cp*Y^2)',
 'identity':'nabla_shear psi = q*eta_b + d_q[B*Y*b^3*q/(J*(A*X^2+Cp*Y^2))]',
 'Y_translation':'nabla_VE psi = d_q F_E - (A/Cp)*(delta*eta_b+3*q^2*dq/J)',
 'normalized_rational_trace':'psi_hat=psi+(3*A*E/Cp)*q^2*dq/J',
 'remaining_physical_residue':'unchanged nonzero adjoint; no closure asserted',
 'certificate':False,
}
Path(__file__).with_name('rational-ruling-trace-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
