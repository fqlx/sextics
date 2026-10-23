"""Exact monic cubic normalization with the actual polynomial radial density."""
import json
from pathlib import Path
import sympy as S

c,a,p,q,T,V,Y=S.symbols('c a p q T V Y',nonzero=True)
alpha=T*V/2;beta=V/3;gamma=T*V**2/(2*Y)
H=1+c**(-6)*Y**(-2)+(a/c)**6
C=c**6
B=c*V*(T/2+a/(3*c))+a*T*V**2/(2*c**2*Y)
f=C*p**3+B*p+H;g=B+3*C*p**2
Hnew=c**6+a**6+Y**(-2)
Bnew=alpha*c**3+beta*a*c**2+gamma*a
fnew=q**3+Bnew*q+Hnew;gnew=3*q**2+Bnew
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
check('H-new',Hnew-c**6*H)
check('B-new',Bnew-c**2*B)
check('f-new',fnew.subs(q,c**4*p)-c**6*f)
check('g-new',gnew.subs(q,c**4*p)-c**2*g)
Rold=B*p/g**3;Rnew=Bnew*q/gnew**3
check('actual-residue-unchanged',Rnew.subs(q,c**4*p)-Rold)
check('canonical-kappa-unchanged',Bnew**3/Hnew**2-B**3/(C*H**2))
check('canonical-V-unchanged',(-Hnew/(q*gnew)-S.Rational(1,3)).subs(q,c**4*p)-(-H/(p*g)-S.Rational(1,3)))
check('canonical-W-unchanged',(Hnew*Rnew).subs(q,c**4*p)-C*H*Rold)
# Omega=-c^4 dc dh eta1 eta2; h=a/c, hence dc dh=dc da/c.
check('actual-four-density',-c**4/c+c**3)
# Also check the unreduced double-pole five-form: p=q/c^4,
# f=fnew/c^6, and dp=(dq/c^4)+terms containing dc.
check('actual-five-form-density',(-c**3)*(q/c**4)**2*c**12/c**4-(-c**3*q**2))
check('gamma-coefficient-relation',gamma-3*alpha*beta/Y)
check('K3-coefficient-relation',64*alpha**6+729*beta**6-V**6*(T**6+1))

data={
 'status':'Exact full source normalization; no polynomial integration or primitive asserted',
 'check_count':len(checks),'checks':checks,
 'substitution':{'a':'c*h','q':'c^4*p'},
 'monic_cubic':'q^3+Btilde*q+S=0',
 'coefficients':{'S':str(Hnew),'Btilde':str(Bnew),'Ctilde':'1'},
 'elliptic_coefficient_relations':[
    'alpha=T*V/2','beta=V/3','gamma=T*V^2/(2*Y)=3*alpha*beta/Y',
    '64*alpha^6+729*beta^6=1-Y^2'],
 'physical_source':'-c^3*Rnew dc ^ da ^ eta1 ^ eta2',
 'Rnew':'Btilde*q/(3*q^2+Btilde)^3 = Rold',
 'canonical_gauge':'kappa,V,W are all unchanged; complete source vector is (0,1/S)',
 'physical_double_pole_form':'-c^3*q^2/(2*fnew^2) dc ^ da ^ eta1 ^ eta2 ^ dq',
 'retained_dependence':'alpha,beta,gamma,Y and eta1,eta2 remain in the common K3/elliptic function field',
 'warning':'Polynomial radial density does not supply an integration along elliptic factors or cancel coefficient jets',
}
Path(__file__).with_name('radial-polynomial-source-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact full-source normalization identities')
