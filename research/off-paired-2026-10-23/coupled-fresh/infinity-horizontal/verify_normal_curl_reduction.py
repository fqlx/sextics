"""Exact rational partial curl of the infinity source; no closure claim."""
import sympy as s
from pathlib import Path
import json
H,C,z=s.symbols('H C z',nonzero=True)
R=s.Function('R')(H,C,z); ell=s.Function('ell')(H,C,z)
def th(f):return C*s.diff(f,C)
def T(f):return s.diff(f,H)+2*C*s.diff(f,C)/(3*H)
# First polynomial: (2theta+3)(46theta²−105theta+70)
# =92theta³−72theta²−175theta+210.
def B(f):
    return (-C**3*(92*th(th(th(f)))-72*th(th(f))-175*th(f)+210*f)/(630*H**2)
            +729*H**2*(23*th(th(th(f)))-18*th(th(f))-107*th(f)+102*f)/(630*C**3))
def zero(f):return s.expand(f)==0
checks=[]
checks.append(zero(T(B(ell))-B(T(ell))))
checks.append(zero(s.diff(B(ell),z)-B(s.diff(ell,z))))
k=s.Rational(81,2)*C**2*z
phi=s.diff(R,H)-k*s.diff(ell,H)
xi=B(s.diff(phi,H))/6
gamma=s.factor(B(th(k)))
checks.append(s.factor(gamma+s.Rational(1386,35)*C**5*z/H**2)==0)
Fplus=s.expand(B(th(k*ell))-gamma*ell)
Kplus=s.expand(B(k*(2*th(th(ell))+5*th(ell)+2*ell))-gamma*ell)
checks.append(Fplus.coeff(ell)==0)
checks.append(Kplus.coeff(ell)==0)
Qstd=B(phi)/6-B(th(R))/(9*H)+Fplus/(9*H)
A=-s.Rational(154,35)*C**5/H**3
g=A*z**2/2
P0=g*T(ell);Q0=g*s.diff(ell,z)
S=B(th(2*th(R)-3*R))/(27*H**2)-Kplus/(27*H**2)+A*z**2*s.diff(ell,z)/(6*H)
checks.append(zero(xi-T(Qstd)-s.diff(P0,z)+T(Q0)-S))
# Actual target normal antiderivative, checked without replacing physical a.
a=s.symbols('a',nonzero=True)
q=3*C-s.Rational(3,2)*a*z
P=a**4+q**6+a**2*(z**6+q*z/2+1-H)
Pa=s.diff(P,a)
Rn=-27*C**3/a+s.Rational(81,4)*C*z**2*a-s.Rational(27,16)*z**3*a**2
Wn=-s.Rational(81,4)*C**2*z**2/a
checks.append(s.cancel(s.diff(Rn,a)+s.diff(Wn,z)-q**3/a**2)==0)
# D_H R−k D_H log a equals q³/Pa.
checks.append(s.cancel((s.diff(Rn,a)-k/a)*a**2/Pa-q**3/Pa)==0)
assert all(checks),checks
out={'checks':len(checks),'passed':True,'gamma':str(gamma),'A':str(A),'certificate':False,'remaining':'explicit nonzero rational S; closure unproved'}
Path(__file__).with_name('normal-curl-reduction-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
