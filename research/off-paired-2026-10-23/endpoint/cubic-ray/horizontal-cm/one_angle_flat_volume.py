"""Exact one-angle finite normalization of the physical G36 base.

This supplies an actual flat physical volume and a simpler CM incidence.
It does not provide a primitive or certificate.
"""
import json
from pathlib import Path
import sympy as S

Z,h,r,nu,eta=S.symbols('Z h r nu eta',nonzero=True)
coords=[Z,h,r,nu]
relation=nu**6+eta**6-1
checks=[]
def reduce(expr):
    num,den=S.fraction(S.cancel(expr))
    rem=S.rem(S.Poly(num,eta),S.Poly(relation,eta)).as_expr()
    return S.cancel(rem/den)
def check(name,expr):
    value=reduce(expr)
    assert value==0,(name,S.factor(value))
    checks.append(name)
def partial(expr,q):
    return S.diff(expr,q)+(S.diff(expr,eta)*(-nu**5/eta**5) if q==nu else 0)

z=1/Z;U=r*nu;K=h*r*eta;t=h**6
old=[z,U,K,t]
Jac=S.Matrix([[partial(value,q)for q in coords]for value in old])
volume=S.factor(Jac.det()/(18*t*z**2))
check('physical-volume-Z-h-r-nu',volume-r/(3*eta**5))
# Rrad=r^2, so dRrad=2r dr; the pulled-back 4-form is
# (1/6) dZ dh dRrad (dnu/eta^5).
check('physical-volume-Z-h-Rrad-theta',volume/(2*r)-1/(6*eta**5))

H=1+z**2+t
C=z**(-2)+U**6+K**6/t
B=U/2+K/3+z*U*K/2
check('H-coefficient',H-(1+Z**(-2)+h**6))
check('C-coefficient',C-(Z**2+r**6))
check('B-coefficient',B-(r*nu/2+h*r*eta/3+h*r**2*nu*eta/(2*Z)))

e=1/(nu**2*eta**2)
w=(nu**6-eta**6)/(nu**3*eta**3)
check('CM-Weierstrass-equation',w**2-e**3+4)
check('CM-angle-differential',partial(e,nu)-2*w/eta**5)

# A sixfold h-root change sends eta -> zeta^-1 eta (nu fixed).
# A sixfold r-root change sends nu,eta -> zeta^-1(nu,eta).
# Character bookkeeping is enough because the transformations are monomial.
characters={
    'h_root':{'h':1,'r':0,'nu':0,'eta':-1,'theta':-1,
              'dH_dC_z_density':1,'balanced_total':0},
    'r_root':{'h':0,'r':1,'nu':-1,'eta':-1,'theta':-2,
              'dH_dC_z_density':2,'balanced_total':0},
}
for name,data in characters.items():
    assert (data['theta']+data['dH_dC_z_density'])%6==0
    checks.append(name+'-physical-density-character')
    monomials=[{'r':1,'nu':1},{'h':1,'r':1,'eta':1},
               {'h':1,'r':2,'nu':1,'eta':1}]
    for j,m in enumerate(monomials):
        assert sum(data[q]*exponent for q,exponent in m.items())%6==0
        checks.append(name+'-B-term-'+str(j))

out={
    'status':'Exact physical one-angle normalization; no current or certificate',
    'constant_scope':'fixed k characteristic zero; use k=C for full contract',
    'checks':checks,'check_count':len(checks),
    'map':{'z':'1/Z','U':'r*nu','K':'h*r*eta','t':'h^6',
           'Rrad':'r^2','angle':'nu^6+eta^6=1'},
    'physical_volume':'(1/6) dZ ^ dh ^ dRrad ^ theta',
    'theta':'dnu/eta^5 = eta*dnu-nu*deta = de/(2*w)',
    'CM_curve':'w^2=e^3-4',
    'CM_coordinates':{'e':'1/(nu^2*eta^2)',
                      'w':'(nu^6-eta^6)/(nu^3*eta^3)'},
    'coefficients':{'H':'1+Z^-2+h^6','C':'Z^2+Rrad^3',
                    'B':'r*nu/2+h*r*eta/3+h*r^2*nu*eta/(2*Z)'},
    'source':'W/(6*C*H) dZ ^ dh ^ dRrad ^ theta, W=C*H*B*p/g^3',
    'root_characters':characters,
}
Path(__file__).with_name('one-angle-flat-volume-results.json').write_text(
    json.dumps(out,indent=2)+'\n')
print('Passed',len(checks),'exact identities/character checks')
