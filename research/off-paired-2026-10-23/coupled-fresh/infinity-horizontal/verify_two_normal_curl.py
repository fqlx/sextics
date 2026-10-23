"""Exact rational source-carrying curl for the two-normal Ore gauge."""
import sympy as s,json
from pathlib import Path
H,C,z=s.symbols('H C z',nonzero=True)
R=s.Function('R')(H,C,z);ell=s.Function('ell')(H,C,z)
def th(f):return C*s.diff(f,C)
def T(f):return s.diff(f,H)+2*C*s.diff(f,C)/(3*H)
def B(f):
 g=th(th(f))-3*th(f)+2*f;g=2*th(g)+3*g
 return (C**3*(44*th(th(g))-35*g)/H**2-729*H**2*(11*th(th(g))-39*g)/C**3)/630
def zero(f):return s.expand(f)==0
k=s.Rational(81,2)*C*C*z
phi=s.diff(R,H)-k*s.diff(ell,H)
checks=[zero(T(B(ell))-B(T(ell))),zero(B(C)),zero(B(C*C)),zero(B(th(k)))]
Q=B(phi)/6-B(th(R))/(9*H)+B(th(k*ell))/(9*H)
S=B(th(2*th(R-k*ell)-3*(R-k*ell)))/(27*H*H)
checks.append(s.expand(Q).coeff(ell)==0)
checks.append(s.expand(S).coeff(ell)==0)
checks.append(zero(B(s.diff(phi,H))/6-T(Q)-S))
# Exact equality with the source-preserving Ore operator from independent construction.
d=json.loads(Path(__file__).with_name('two-normal-gauge.json').read_text())
cs=[s.sympify(x,locals={'H':H,'C':C})for x in d['B12']]
checks.append(zero(B(ell)-sum(x*s.diff(ell,C,j)for j,x in enumerate(cs))))
assert all(checks),checks
out={'checks':len(checks),'passed':True,'certificate':False,'current':'xi=TQ+S, all Q,S rational after cancellation of undifferentiated ell','remaining':'source-specific integration of S'}
Path(__file__).with_name('two-normal-curl-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
