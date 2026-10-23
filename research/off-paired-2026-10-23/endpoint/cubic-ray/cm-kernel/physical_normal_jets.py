"""Exact physical normal normalization for the parity-correct CM jets."""
import json
from pathlib import Path
import sympy as S

c,h,H,B,b1,k,x,a_scale=S.symbols('c h H B b1 k x a_scale',nonzero=True)
s=x**3
R0=-64*s*(s-64)/(s+128)**3
R=R0/(c**6*H)
J=H*b1-4*B*h**5
x_h=4*x**3*J/(c**2*H*k**2*(s+128))
m=c**4*R/(2*a_scale*x*x_h)
m_simplified=-8*k**2*(s-64)/(a_scale*x*(s+128)**2*J)
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
check('normalization-m',m-m_simplified)
check('target-principal-source',2*m*x*x_h-c**4*R/a_scale)
check('J-normal-derivative',(S.diff(J,h)+S.diff(J,H)*6*h**5+S.diff(J,B)*b1)-2*h**4*(h*b1-10*B))
def Dh(f):
    return S.diff(f,h)+6*h**5*S.diff(f,H)+b1*S.diff(f,B)+(2*k*h**5/H)*S.diff(f,k)+x_h*S.diff(f,x)
m_h=S.factor(Dh(m_simplified))
check('full-normal-log-derivative',m_h-m_simplified*((3*x**2/(s-64)-1/x-6*x**2/(s+128))*x_h+4*h**5/H-2*h**4*(h*b1-10*B)/J))

# The rational cubic variable p fixes x=-4*k/(c^2*p), k^3=H.
p,C=S.symbols('p C',nonzero=True)
f=C*p**3+B*p+H;g=B+3*C*p**2;Delta=4*B**3+27*C*H**2
def remp(value):
    num,den=S.fraction(S.cancel(value))
    return S.cancel(S.rem(S.Poly(num,p),S.Poly(f,p)).as_expr()/den)
sv=-64*H/(C*p**3)
m0=-c**4*p**2*(sv-64)/(2*a_scale*(sv+128)**2*J)
value=remp(m0*sv-c**4*B*H*p/(2*a_scale*g**2*J))
check('traced-pair-actual-normal-current',value)
inv_g2=S.invert(S.Poly(g**2,p),S.Poly(f,p)).as_expr()
reduced=S.rem(S.Poly(p*inv_g2,p),S.Poly(f,p)).as_expr()
trace=3*reduced.coeff(p,0)-2*B/C*reduced.coeff(p,2)
check('trace-p-over-g2',trace+9*H/Delta)

data={
 'status':'Complete physical first-normal-jet current and retained nonzero derivative; no closure',
 'check_count':len(checks),'checks':checks,
 'physical_coefficients':{
    'H':'1+c^-6*Y2^-2+h^6','C':'c^6',
    'B':'c*V*(T/2+h/3)+h*T*V^2/(2*c*Y2)',
    'b1':'B_h=c*V/3+T*V^2/(2*c*Y2)'},
 'normalization':{'J':str(J),'x3_h':str(x_h),'m':str(m_simplified),
                  'm_h':str(m_h)},
 'paired_current':'Gamma=m*(zeta^2*x1^2-x3^2)*eta1^dc^eta2',
 'paired_divergence':'R-a_scale*(zeta^2*x1^2-x3^2)*m_h/c^4',
 'after_H_root_trace':{
    'current':'-c^4*B*H*p/(2*a_scale*g^2*J)*eta1^dc^eta2',
    'trace_zero_current':'-c^4*B*H/(2*a_scale*J)*(p/g^2+3*H/Delta)*eta1^dc^eta2',
    'warning':'Subtracting the cubic field trace also subtracts its differentiated remainder; it does not erase the trace-free error.'},
 'mixed_normal_status':'No mixed c/E2 correction has closed the density derivative. Both individual CM graph currents and their errors are retained.',
}
Path(__file__).with_name('physical-normal-jets-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact physical-normal and trace identities')
