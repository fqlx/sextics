"""Exact h-to-Fermat-angle transfer of the fresh source-carrying current.

This checks a correction step with the monomial bracket {H,C}. It cancels
the F0 term but does not close the primitive: its apparent constant R
coefficient cancels as well. No exclusion or certificate is asserted.
"""
import json
from pathlib import Path
import sympy as S

Z,h,u,v=S.symbols('Z h u v',nonzero=True)
H=1+Z**(-2)+h**6
C=Z**2+u**6+v**6
B=u/2+h*v/3+h*u*v/(2*Z)
b=S.diff(B,h)
coords=[Z,h,u,v]
bracket=lambda f,g:S.diff(f,Z)*S.diff(g,h)-S.diff(f,h)*S.diff(g,Z)+S.diff(f,u)*S.diff(g,v)-S.diff(f,v)*S.diff(g,u)
angle=lambda f:6*v**5*S.diff(f,u)-6*u**5*S.diff(f,v)
E1=S.factor(angle(b));E=S.factor(bracket(B,C));D=-12*Z*h**5
coefficient=1/(4*Z*b)
X_C=S.Matrix([0,-2*Z,6*v**5,-6*u**5])
J0=S.Matrix([0,1/(2*b),0,0])
J1=coefficient*X_C
div=lambda vec:sum(S.diff(vec[i],coords[i])for i in range(4))
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
check('B-affine-h',B-u/2-h*b)
check('C-H-monomial',bracket(H,C)-D)
check('angle-C',angle(C))
check('angle-H',angle(H))
check('angle-B',angle(B)-(3*v**5+h*E1))
check('full-C-B',E-(-2*Z*b+3*v**5+h*E1))
for i,target in enumerate([0,0,6*v**5*coefficient,-6*u**5*coefficient]):
    check('combined-current-vector-'+str(i),(J0+J1)[i]-target)
check('F0-cancellation',-30*h**5/b-10*D*coefficient)
check('combined-R-coefficient',1+2*E*coefficient-(3*v**5+h*E1)/(2*Z*b))
check('combined-q-coefficient',div(J0+J1)+E1/(4*Z*b**2))
data={
 'status':'Actual partial-current transfer; no closure or nonexistence claim',
 'checks':checks,'check_count':len(checks),
 'notation':{'q':'p_B=-p/g','F0':'(3*C*p^2-B)/(10*g^3)=-q_H/10',
             'R':'B*p/g^3','b':'B_h=v/3+u*v/(2*Z)',
             'X_angle':'6*v^5*d_u-6*u^5*d_v',
             'E1':str(E1)},
 'first_current':'q*d_h/(2*b)',
 'first_divergence':'R-30*h^5*F0/b',
 'added_current':'q*X_C/(4*Z*b), X_C=-2*Z*d_h+X_angle',
 'combined_current':'q*X_angle/(4*Z*b)',
 'combined_divergence':'(3*v^5+h*E1)*R/(2*Z*b)-E1*q/(4*Z*b^2)',
 'gap':'F0 cancels, but the constant R coefficient cancels too; full remaining R and q terms must be retained',
 'density':'all scalar divergence identities are relative to actual Omega=-dZ dh du dv/3',
}
Path(__file__).with_name('horizontal-monomial-transfer-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact source-transfer coefficient identities')
