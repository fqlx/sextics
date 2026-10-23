#!/usr/bin/env python3
"""Independent generic Morse-coordinate cubic lift audit."""
import json
from pathlib import Path
import sympy as s

i,J,t=s.symbols('i J t',nonzero=True)
V=s.Function('V')(i,J)
g=s.Function('g')(i,J)
h=s.Function('h')(i,J)
p=s.diff(V,i);q=s.diff(V,J)
v=V+t*t
def A(x):return s.diff(x,i)-p*s.diff(x,t)/(2*t)
def B(x):return s.diff(x,J)-q*s.diff(x,t)/(2*t)
def Z(x):return v*s.diff(x,t)/(2*t)
def D(x):return 6*Z(x)-2*i*A(x)-2*J*B(x)
def L3(x):
    y=Z(x)+D(x)/2+5*x
    y=Z(y)
    y=Z(y)+J*B(y)+2*y
    return s.expand(A(A(A(x)))+v*y)

hh=V-J*q
ww=4*V+i*p+J*q
sigma=(-p**3+V*V*hh*ww)/8
Tg=s.Rational(3,8)*((6*p*p-2*i*V*V*hh)*s.diff(g,i)
    +2*J*V*V*(ww-hh)*s.diff(g,J)
    +(6*p*s.diff(V,i,2)+2*V*J*(q*ww+V*s.diff(ww,J))
      +3*V*V*ww+22*V*V*hh)*g)
expr=L3(g*t**3+h*t**5)
checks={}
def check(name,x):
    y=s.expand(x)
    assert y==0,(name,y)
    checks[name]=True
check('cubic_leading_map',expr.coeff(t,-3)+3*sigma*g)
check('cubic_lower_map',expr.coeff(t,-1)-Tg-15*sigma*h)
check('no_other_negative_powers',sum(term for term in s.Add.make_args(expr)
      if term.as_powers_dict().get(t,0)<0)-expr.coeff(t,-3)*t**(-3)-expr.coeff(t,-1)/t)
out={'status':'Generic exact fold lift audit; actual global interpolation not asserted',
     'coordinates':'t^2=v-V(i,J)',
     'sigma':str(sigma),'Tg':str(Tg),'checks':checks,'count':len(checks)}
path=Path(__file__).with_name('fold-lower-map-audit.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':all(checks.values()),'output':str(path)}))
