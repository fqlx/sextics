"""Exact CM diagonal kernel, parity correction, and first normal jets.

All polynomial checks are performed in a fixed common function field.
The physical normalization has a retained density-derivative remainder.
No primitive of the immutable target is asserted.
"""
import json
from pathlib import Path
import sympy as S

x1,x,y1,y,zeta,ss=S.symbols('x1 x y1 y zeta ss',nonzero=True)
relations=[y1**2-x1**3+16,y**2-x**3+16,zeta**2+zeta+1]
GB=S.groebner(relations,y1,y,zeta,domain=S.QQ.frac_field(x1,x,ss))
checks=[]
def reduce(value):
    num,den=S.fraction(S.cancel(value))
    return S.cancel(GB.reduce(num)[1]/den)
def check(name,value):
    result=reduce(value)
    assert result==0,(name,S.factor(result))
    checks.append(name)
def D1(f):return 2*y1*S.diff(f,x1)+3*x1**2*S.diff(f,y1)
def D3(f):return 2*y*S.diff(f,x)+3*x**2*S.diff(f,y)
def d_one(form):
    # form=A*eta1+B*eta3; result is coefficient of eta1^eta3.
    A,B=form
    return D1(B)-D3(A)

K=(y1+y)/(x1-x)
check('zeta-kernel-D1',D1(K)-(2*x1+x-K**2))
check('zeta-kernel-D3',D3(K)-(K**2-x1-2*x))
check('base-kernel',d_one([K,-K])-(x-x1))
Kt=(y1+y)/(x1-zeta*x)
P=[(Kt-zeta*K)/(zeta**2-zeta),
   (-zeta*Kt+zeta*K)/(zeta**2-zeta)]
check('CM-projected-kernel',d_one(P)-x)

L=(x1-x)*(x1-zeta*x)
Pminus=[-zeta**2*y*(x1+zeta**2*x)/L,-x*y1/L]
Pplus=[-zeta**2*y1*(x1+zeta**2*x)/L,-x*y/L]
for j in range(2):
    # sigma3 sends y->-y and eta3->-eta3.
    sigma=P[j].subs(y,-y)*(-1 if j else 1)
    check('odd-projection-'+str(j),Pminus[j]-(P[j]-sigma)/2)
    check('even-projection-'+str(j),Pplus[j]-(P[j]+sigma)/2)
check('odd-kernel-differential',d_one(Pminus)-x)
check('even-kernel-closed',d_one(Pplus))

alpha0=[y*v for v in Pminus]
alpha1=[y1*v for v in Pplus]
C0=x*(x1+2*zeta**2*x)**2/(2*L)
C1=-3*x1**2*x/(2*L)
check('odd-jet-0',d_one(alpha0)-2*y*C0)
check('odd-jet-1',d_one(alpha1)-2*y*C1)
check('jet-difference-eta1',alpha0[0]-alpha1[0]-(zeta**2*x1**2-x**2))
check('jet-difference-eta3',alpha0[1]-alpha1[1])
check('jet-source-difference',C0-C1-2*x)
for i,form in enumerate([alpha0,alpha1]):
    check('jet-even-eta1-'+str(i),form[0].subs(y,-y)-form[0])
    check('jet-even-eta3-'+str(i),-form[1].subs(y,-y)-form[1])

# After replacing eta3=dx/(2y), the currents already lie in the
# sigma3-fixed field; there is no hidden odd coefficient left.
A0=-zeta**2*(x**3-16)*(x1+zeta**2*x)/L
A1=-zeta**2*(x1**3-16)*(x1+zeta**2*x)/L
Bdx=-x*y1/(2*L)
check('jet0-rational-eta1',alpha0[0]-A0)
check('jet1-rational-eta1',alpha1[0]-A1)
check('jet0-rational-dx',alpha0[1]-2*y*Bdx)
check('jet1-rational-dx',alpha1[1]-2*y*Bdx)

def root_trace_function(value):
    return sum(value.subs(x,zeta**j*x) for j in range(3))/3
def root_trace_dx_coefficient(value):
    return sum(zeta**j*value.subs(x,zeta**j*x) for j in range(3))/3
s=x**3;Q=x1**3
Z0_A=s*(s-16)/(Q-s)
Z1_A=s*(Q-16)/(Q-s)
Z_B=-x1*y1/(6*(Q-s))
check('root-trace-jet0-eta1',root_trace_function(x*A0)-Z0_A)
check('root-trace-jet1-eta1',root_trace_function(x*A1)-Z1_A)
check('root-trace-common-ds',root_trace_dx_coefficient(x*Bdx)-3*x**2*Z_B)
Z0_A_s=ss*(ss-16)/(Q-ss)
Z1_A_s=ss*(Q-16)/(Q-ss)
Z_B_s=-x1*y1/(6*(Q-ss))
check('traced-jet0-differential',D1(Z_B_s)-S.diff(Z0_A_s,ss)-(Q-6*ss+32)/(6*(Q-ss)))
check('traced-jet1-differential',D1(Z_B_s)-S.diff(Z1_A_s,ss)+(5*Q-32)/(6*(Q-ss)))

data={
 'status':'Parity-correct actual CM kernel jets with a retained physical density derivative; no certificate',
 'constant_scope':'fixed k characteristic zero containing zeta3; use k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'curves':'y1^2=x1^3-16; y3^2=x3^3-16',
 'differentials':'eta1=dx1/(2y1), eta3=dx3/(2y3)',
 'L':'(x1-x3)(x1-zeta*x3)',
 'jet0':{'A_eta1':str(A0),'B_dx3':str(Bdx),'d_coefficient_eta1_dx3':str(C0)},
 'jet1':{'A_eta1':str(A1),'B_dx3':str(Bdx),'d_coefficient_eta1_dx3':str(C1)},
 'difference':'alpha0-alpha1=(zeta^2*x1^2-x3^2)*eta1',
 'source_difference':'d(alpha0-alpha1)=2*x3*eta1^dx3',
 'physical_frame':'Omega=-c^4/a_scale dc^dh^eta1^eta2; a_scale=2^(-1/3)',
 'normalization':'m=c^4*R/(2*a_scale*x3*x3_h)',
 'actual_current':'Gamma=m*(alpha0-alpha1)^dc^eta2',
 'actual_divergence':'R-a_scale*(zeta^2*x1^2-x3^2)*m_h/c^4',
 'individual_errors':'For Gamma_i=m*alpha_i^dc^eta2, error_i=-a_scale/c^4*[m_h*(A_i+B_dx*x3_1)-m_1*B_dx*x3_h]; principal source=(C_i/(2*x3))*R',
 'derivatives':'m_h,m_1 are complete physical derivatives at fixed c,E2; x3_h,x3_1 include all H,B variations',
 'gap':'The mixed normal corrections to the nonzero m_h term remain open. The paired graph poles cancel, so this first pair alone gives no new Gysin closure.',
 'H_cube_root_trace':{
   'm0':'m/x3=-c^4*p^2*(s-64)/(2*a_scale*(s+128)^2*J), J=H*B_h-4*B*h^5',
   's':'x3^3=-64*H/(c^6*p^3)',
   'Q':'x1^3=4*(u^6+v^6)^2/(u^6*v^6)',
   'Z0':'s*(s-16)/(Q-s)*eta1-x1*y1/(6*(Q-s))*ds',
   'Z1':'s*(Q-16)/(Q-s)*eta1-x1*y1/(6*(Q-s))*ds',
   'current_i':'Gamma_i_bar=m0*Zi^dc^eta2',
   'difference':'Gamma_0_bar-Gamma_1_bar=-m0*s*eta1^dc^eta2',
   'remark':'Each individual traced current retains the actual CM graph pole Q-s; the paired difference cancels it.',
 },
}
Path(__file__).with_name('odd-kernel-jets-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact kernel, parity and odd-jet identities')
