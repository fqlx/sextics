"""Geometric rational S3 cover of kappa and actual normalized source.

The deck action is over constants containing a cube root of unity. These
universal identities do not integrate the physical density.
"""
import sympy as S,json
from pathlib import Path
q,zeta=S.symbols('q zeta');k=-27*q**3/(q**3+1)**2
F=(q*q-q+1)/(3*(q*q+q+1));V=F-S.Rational(1,3)
W=q*(q+1)**2*(q*q-q+1)/(9*(q*q+q+1)**3)
checks=[]
def check(name,e):
 assert S.cancel(e)==0,(name,S.factor(e));checks.append(name)
def zcheck(name,e):
 n,d=S.fraction(S.cancel(e));assert S.rem(n,zeta*zeta+zeta+1,zeta)==0,name;checks.append(name)
theta=lambda a:S.cancel(k/S.diff(k,q)*S.diff(a,q))
check('F-cubic',(4*k+27)*F**3-(4*k+27)*F**2+9*F-1)
check('V-definition',V+2*q/(3*(q*q+q+1)))
check('theta-V',theta(V)+2*W)
check('theta-W',theta(W)-3*V/(4*k+27)-(27-2*k)*W/(4*k+27))
for name,e in [('kappa',k),('F',F),('W',W)]:check(name+'-inversion',e.subs(q,1/q)-e)
zcheck('kappa-cyclic',k.subs(q,zeta*q)-k)
zcheck('V-cyclic-trace',V+V.subs(q,zeta*q)+V.subs(q,zeta**2*q))
zcheck('W-cyclic-trace',W+W.subs(q,zeta*q)+W.subs(q,zeta**2*q))
H,B=S.symbols('H B');C=-B**3*(1+q**3)**2/(27*H**2*q**3)
p=3*H*q/(B*(q*q-q+1));g=B+3*C*p*p
check('actual-cubic',C*p**3+B*p+H)
check('F-source-binding',F+H/(p*g))
check('W-source-binding',W-C*H*B*p/g**3)
data={'checks':checks,'check_count':len(checks),'constant_field':'k containing zeta3; k=C for full contract',
 'kappa':str(k),'F':str(F),'V':str(S.factor(V)),'W':str(W),
 'p':str(p),'deck':['q -> zeta3*q','q -> 1/q'],
 'geometric_branch_signature':[3,2,2],
 'incidence':'q=S/T, S^3+T^3=H, B+3cST=0,c^3=C,p=-(S+T)/c',
 'status':'geometric rational Galois cover and full source binding; no physical density primitive'}
Path(__file__).with_name('rational-kappa-cover-results.json').write_text(json.dumps(data,indent=2));print('Passed',len(checks),'exact identities')
