"""Exact selected-sheet normalizer and its CM 3-isogeny factor.

This identifies the actual pole on D, without asserting a source closure.
"""
import json
from pathlib import Path
import sympy as S

lam,kappa,x,y,H,C,u,B=S.symbols('lam kappa x y H C u B',nonzero=True)
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)

gu=B+3*C*u**2
graph_kappa=-(1+lam)**3/lam
check('selected-sheet-normalizer',
      (gu*u-H*(2*lam-1)).subs(B,-H*(1+lam)/u).subs(C,lam*H/u**3))
check('normalizer-norm-on-graph',
      graph_kappa+27*lam**2-(2*lam-1)*(13*lam**2+5*lam+1)/lam)
norm=S.prod(B+3*C*u**2*z for z in [1,(-1+S.sqrt(3)*S.I)/2,(-1-S.sqrt(3)*S.I)/2])
check('normalizer-full-norm',S.expand(norm)-B**3-27*C**3*u**6)

xp=(x**3-64)/x**2
yp=y*(x**3+128)/x**3
check('standard-three-isogeny',
      S.rem(S.together(yp**2-xp**3-432).as_numer_denom()[0],y**2-x**3+16,y))
check('actual-CM-graph-kappa',
      graph_kappa.subs(lam,-64/x**3)-(xp/4)**3)
check('selected-pole-is-isogeny-two-torsion',
      (2*lam-1).subs(lam,-64/x**3)+(x**3+128)/x**3)
check('cubic-discriminant-is-isogeny-y-square',
      S.rem(S.together(4*(xp/4)**3+27-yp**2/16).as_numer_denom()[0],y**2-x**3+16,y))

data={
 'status':'Exact normalizer-pole geometry for the actual selected CM graph; no correction closure',
 'check_count':len(checks),'checks':checks,
 'graph':'u^3=lambda*H/C, D=H+B*u+C*u^3=0',
 'selected_gu':'g_u=B+3*C*u^2=H*(2*lambda-1)/u on D',
 'full_normalizer_norm':'Norm_u(g_u)=C*H^2*(kappa+27*lambda^2)',
 'norm_restriction':'(kappa+27*lambda^2)|D=(2*lambda-1)*(13*lambda^2+5*lambda+1)/lambda',
 'actual_CM_lambda':'lambda=-64/x1^3',
 'isogeny':'(x1,y1) -> (x1-64/x1^2, y1*(1+128/x1^3)), E1:y1^2=x1^3-16 -> Eprime:yprime^2=xprime^3+432',
 'interpretation':'The selected-sheet normalizer pole lambda=1/2 is x1^3=-128 and maps to yprime=0, a target 2-torsion point. The elliptic isogeny itself is unramified; only its x-coordinate map has a branch there.',
 'warning':'The quadratic factor in the traced norm comes from the other two u sheets. It is not an additional selected-sheet pole. Keeping the finite u extension until completing a current may preserve this distinction. No automatic cancellation is asserted.',
}
Path(__file__).with_name('normalizer-isogeny-factor-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact normalizer and isogeny identities')
