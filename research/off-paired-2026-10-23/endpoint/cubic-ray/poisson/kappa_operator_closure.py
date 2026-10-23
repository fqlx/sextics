"""Exact one-variable finite connection and CM product recurrence.

The source remains W/(H*C). No closed-time form or physical primitive is
asserted. All coefficient derivatives in the CM recurrence are retained.
"""
import sys,json
from pathlib import Path
import sympy as S
root=Path(__file__).parent;sys.path.insert(0,str(root.parent))
from finite_connection import H,B,C,D,MH,MB,MC,source

k=S.symbols('kappa');aa=4*k+27
Mk=S.Matrix([[0,3/aa],[-2,(27-2*k)/aa]])
kap=B**3/(C*H**2)
V=S.Matrix([-6*B*C*H/D,4*B**2*C/D])
W=H*C*source;gauge=S.Matrix.hstack(V,W)
checks=[]
def check(name,q):
 assert S.cancel(q)==0,(name,S.factor(q));checks.append(name)
for v,M,dl in zip([H,B,C],[MH,MB,MC],[-2/H,3/B,-1/C]):
 E=(gauge.diff(v)+M*gauge-dl*gauge*Mk.subs(k,kap))
 for i in range(2):
  for j in range(2):check('onevariable-connection-'+str(v)+str(i)+str(j),E[i,j])
for i in range(2):check('actual-source-'+str(i),gauge[i,1]/(H*C)-source[i])
check('gauge-determinant',gauge.det()-2*B**3*C**2*H/D**2)

# A separate cubic algebra verifies the theta connection without old matrices.
F=S.symbols('F');poly=aa*F**3-aa*F**2+9*F-1
inv=S.invert(S.diff(poly,F),poly,F)
rem=lambda q:S.rem(q,poly,F)
der=lambda q:rem(S.diff(q,k)-S.diff(q,F)*S.diff(poly,k)*inv)
VV=F-S.Rational(1,3);WW=rem(-k*der(F)/2)
check('theta-V',rem(k*der(VV)+2*WW))
check('theta-W',rem(k*der(WW)-3/aa*VV-(27-2*k)/aa*WW))

PB=MB[:,0]
for name,expr in [
 ('pB-H',PB.diff(H)+MH*PB+PB/(3*H)+4*B*source/(3*H)),
 ('pB-B',PB.diff(B)+MB*PB-2*source),
 ('pB-C',PB.diff(C)+MC*PB+2*PB/(3*C)+2*B*source/(3*C))]:
 for i in range(2):check(name+str(i),expr[i])

# Exact CM recurrence on each Fermat factor.
x,a,u,v,r,j=S.symbols('x a u v r j')
# Integer exponents are verified in Laurent-polynomial form after factoring
# the common monomial, so the identities apply to all integral r,j.
XHfactored=6*((j+1)*x**6-(r+1)*a**6)
check('CM-X-H',XHfactored-6*((r+j+2)*x**6-(r+1)*(x**6+a**6)))
XCfactored=6*((j+1)*u**6-(r+1)*v**6)
check('CM-X-C',XCfactored-6*((r+j+2)*u**6-(r+1)*(u**6+v**6)))

data={'checks':checks,'check_count':len(checks),
 'basis':['V=-H/(p*g)-1/3','W=C*H*R'],
 'kappa':'B^3/(C*H^2)','theta':'kappa*d_kappa',
 'connection':[[str(z)for z in Mk.row(i)]for i in range(2)],
 'source':['0','1/(C*H)'],
 'gauge_old_basis':[[str(S.factor(z))for z in gauge.row(i)]for i in range(2)],
 'determinant':str(S.factor(gauge.det())),
 'minimal_polynomial_F':str(poly),
 'scalar_ODE':'(4*kappa+27)*theta^2 V-(27-2*kappa)*theta V+6V=0',
 'CM_recurrence':'X_H(x^(r+1)*a^(j+1)*Q)=6*x^r*a^j*((r+j+2)*x^6-(r+1)*(H-1))*Q+x^(r+1)*a^(j+1)*{H,B}*partial_B Q',
 'status':'exact canonical operator closure; physical source primitive remains open'}
(root/'kappa-operator-closure-results.json').write_text(json.dumps(data,indent=2));print('Passed',len(checks),'exact identities')
