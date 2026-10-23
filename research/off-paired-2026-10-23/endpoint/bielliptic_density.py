"""Exact identities retaining the physical dx/v density through two elliptic quotients."""
import sympy as s,json
from pathlib import Path
u,V,alpha,w,R,x,v,t,b,B,c,a,h=s.symbols('u V alpha w R x v t b B c a h')
xi=u+1/u;f=u**6+alpha*u**3+1
checks=[]
for sign in [1,-1]:
 eta=V*(u+sign)/u**2
 E=eta**2-(xi+sign*2)*(xi**3-3*xi+alpha)
 assert s.cancel(E.subs(V**2,f))==0
 checks.append(f'elliptic-quotient-{sign}')
 assert s.cancel(s.diff(xi,u)/eta-(u-sign)/V)==0
 checks.append(f'differential-{sign}')
# Curve substitution v=x*w, t=x^3 gives t^2+(w^3-b)t-B=0.
Rexpr=2*t+w**3-b
assert s.rem(s.expand(Rexpr**2-(w**3-b)**2-4*B),t**2+(w**3-b)*t-B,t)==0
checks.append('physical-genus2-curve')
# Its implicit derivative gives dt/(3tw)=-w dw/R.
assert s.cancel((-3*w**2*t/Rexpr)/(3*t*w)+w/Rexpr)==0
checks.append('physical-density')
# Scaling w=a*u,R=h*V,a^3=h turns sextic into u^6-2b/h*u^3+1.
scaled=s.expand((a*u)**6-2*b*(a*u)**3+c)
assert s.cancel((scaled-h**2*(u**6-2*b*u**3/h+1)).subs(c,h**2).subs(a**6,h**2).subs(a**3,h))==0
checks.append('scaling')
# phi dC=-dx/(6v)=w dw/(6R), producing a^2/(12h) sum elliptic forms.
assert s.cancel(a**2*u/(6*h*V)-a**2/(12*h)*((u-1)/V+(u+1)/V))==0
checks.append('actual-density-split')
out={'checks':checks,'count':len(checks),'physical_density':'phi dC = -dx/(6v) = a^2/(12h)*(dxi/eta_plus + dxi/eta_minus)', 'extensions':'c=b^2+4B, h^2=c, a^3=h; generically nonzero', 'elliptic_curves':'eta_plus^2=(xi+2)(xi^3-3xi-2b/h); eta_minus^2=(xi-2)(xi^3-3xi-2b/h)', 'status':'exact source transport only; no scalar primitive or certificate'}
Path(__file__).with_name('bielliptic-density-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
