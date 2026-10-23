"""Exact genuine H/q/z/p current for the whole five-row mixed source.

This proves an explicit source transport, not rational invertibility of its
endpoint defect operator.
"""
import json
from pathlib import Path
import sympy as S
D,z,q,H,C,p,w,Z,sv,dv=S.symbols('D z q H C p w Z sv dv')
B=-z/2
P=(D+B*q)**2-4*q**6
Delta=4*B**6-729*D**4
P4=(3*D**2*z**4/S.Integer(128)-D*z**5*q/256+z**6*q*q/768
    -81*D**3*z*q**3/16-27*D**2*z*z*q**4/16)/Delta
N=P4/w
checks=[]
def reduce_square(value,var,square):
    n,den=S.fraction(S.cancel(value))
    n=S.rem(n,var**2-square,var)
    return S.cancel(n/den)
def check(label,value):
    assert S.cancel(value)==0,(label,S.factor(value))
    checks.append(label)
EP=3*D*S.diff(P,D)+2*z*S.diff(P,z)
EN=(3*D*S.diff(P4,D)+2*z*S.diff(P4,z))/w-P4*EP/(2*w**3)
tq=(P4+q*S.diff(P4,q))/w-q*P4*S.diff(P,q)/(2*w**3)
check('whole-five-row-source-weight-zero',reduce_square(EN+tq,w,P))
Ps=2*q**3+B*q+D
Pd=-2*q**3+B*q+D
Cphys=q/3+z*(sv+dv)/4
CH=z*(1/sv+1/dv)/8
Cq=S.Rational(1,3)+z*(S.diff(Ps,q)/sv+S.diff(Pd,q)/dv)/8
Cz=(sv+dv)/4+z*(-q/2-6*z**5)*(1/sv+1/dv)/8
EH=3*D+12*z**6
EC=EH*CH+q*Cq+2*z*Cz
G=S.groebner([sv*sv-Ps,dv*dv-Pd],sv,dv,domain=S.QQ.frac_field(D,z,q))
n,den=S.fraction(S.cancel(EC-(q/3+7*z*(sv+dv)/8)))
check('actual-physical-endpoint-C-Euler-velocity',G.reduce(n)[1])
check('actual-H-Euler-defect',(3*D+12*z**6-3*H).subs(H,D+1+z**6)-(9*z**6-3))
check('actual-C-Euler-defect',q/3+7*z*(sv+dv)/8-2*Cphys-(-q/3+3*z*(sv+dv)/8))
PE=(H+C*p)**2-4*p**6
f=-p*(H+C*p)/Z**3
tf=p*f
def dh(a):return S.diff(a,H)+S.diff(a,Z)*(H+C*p)/Z
def dc(a):return S.diff(a,C)+S.diff(a,Z)*p*(H+C*p)/Z
def dp(a):return S.diff(a,p)+S.diff(a,Z)*(C*(H+C*p)-12*p**5)/Z
check('literal-endpoint-C-derivative-Euler-transgression',
      reduce_square(3*H*dh(f)+2*C*dc(f)+4*f+dp(tf),Z,PE))
# The full finite compact connection obeys the same identity modulo this
# explicit p-exact transgression. Check every one of its four rows.
data=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
def mat(k):
    return S.Matrix([[S.sympify(x,locals={'H':H,'C':C}) for x in col]for col in data[k]['columns']]).T
MH,MC=mat('H'),mat('C')
F=MC[:,0]
FH=F.diff(H)+MH*F
FC=F.diff(C)+MC*F
assert all(S.cancel(x)==0 for x in 3*H*FH+2*C*FC+4*F)
checks.append('all-four-compact-endpoint-Euler-rows')
out={'status':'Exact whole mixed source Euler current and defect; no inverse/primitive claim',
     'checks':checks,'source':'N*F, N=P4(q)/w, F=∇C omega0',
     'coefficient_currents':{'H':'(3D+12z^6)*N*F','q':'q*N*F','z':'2z*N*F'},
     'literal_current':'-(3D+12z^6)*N*F^dq^dz+q*N*F^dH^dz-2z*N*F^dH^dq+N*tF*dH^dq^dz',
     'fiber_primitive_tF':'-p^2*(H+C*p)/Z^3',
     'exact_identity':'N*F=d(current)-N*((9z^6-3)*FH+(-q/3+3za/4)*FC)^dH^dq^dz',
     'a':'(s+d)/2',
     'defect_operator':'1+(9z^6-3)*∇H+(-q/3+3za/4)*∇C, applied to F',
     'scope':'All physical H,q,z derivatives, all compact rows, all five background rows; explicit p-exact correction retained'}
Path(__file__).with_name('full-mixed-euler-current.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed',len(checks),'exact whole-source physical-Euler and all-component checks')
