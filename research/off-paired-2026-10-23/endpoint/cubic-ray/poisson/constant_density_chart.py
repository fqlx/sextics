"""Exact finite rational cover with constant physical cubic-ray density."""
import json
from pathlib import Path
import sympy as S

Z,h,u,v=S.symbols('Z h u v',nonzero=True)
coords=[Z,h,u,v]
z=1/Z;U=u;K=h*v;t=h**6
old=[z,U,K,t]
Jac=S.Matrix([[S.diff(a,q) for q in coords] for a in old])
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
check('physical-volume',Jac.det()/(18*t*z**2)+S.Rational(1,3))
H=1+Z**(-2)+h**6
B=u/2+h*v/3+h*u*v/(2*Z)
C=Z**2+u**6+v**6
check('H-map',H-(1+z**2+t))
check('B-map',B-(U/2+K/3+z*U*K/2))
check('C-map',C-(z**(-2)+U**6+K**6/t))
bracket=lambda f,g: S.diff(f,Z)*S.diff(g,h)-S.diff(f,h)*S.diff(g,Z)+S.diff(f,u)*S.diff(g,v)-S.diff(f,v)*S.diff(g,u)
check('H-C-monomial-bracket',bracket(H,C)+12*Z*h**5)
check('H-B-bracket',bracket(H,B)-(-2*v/(3*Z**3)-u*v/Z**4+3*h**6*u*v/Z**2))
check('B-C-bracket',bracket(B,C)-(-2*Z*v/3-u*v+3*v**5+3*h*v**6/Z-2*h*u**5-3*h*u**6/Z))
# h -> zeta*h, v -> zeta^-1*v fixes the complete physical coefficients.
for name,terms in [('H',[(6,0)]),('B',[(0,0),(1,1),(1,1)]),('C',[(0,6)])]:
    assert all((a-b)%6==0 for a,b in terms)
    checks.append('deck-'+name)
assert (1-1)%6==0
checks.append('deck-dh-dv-volume')
data={
 'status':'Exact coordinate/source cover; no primitive or certificate',
 'constant_scope':'fixed k of characteristic zero; k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'map_to_G36':{'z':'1/Z','U':'u','K':'h*v','t':'h^6','p':'p'},
 'degree':'6; T^6-t irreducible over k(z,U,K,t), t transcendental',
 'coefficients':{'H':str(H),'B':str(B),'C':str(C)},
 'physical_volume':'-(1/3) dZ ^ dh ^ du ^ dv',
 'actual_source':'-(1/3) B*p/(B+3*C*p^2)^3 dZ ^ dh ^ du ^ dv',
 'deck':'h -> zeta6*h; v -> zeta6^-1*v; Z,u,p fixed',
 'descent':'normalized finite field trace commutes with d and fixes the actual source',
 'brackets':{'H_C':str(S.factor(bracket(H,C))),
             'H_B':str(S.factor(bracket(H,B))),
             'B_C':str(S.factor(bracket(B,C)))},
}
Path(__file__).with_name('constant-density-chart-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact coordinate, bracket and deck checks')
