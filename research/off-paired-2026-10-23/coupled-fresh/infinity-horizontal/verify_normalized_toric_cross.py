"""Literal normalized cross rows, with explicit rational fiber primitives."""
import json
from pathlib import Path
import sympy as s
a,b,q,c,d,e=s.symbols('a b q c d e',nonzero=True)
Q=a*a+b*b+c*q*q+d*a*q+e*q+1
J=2*a*a+d*a*q-2*b*b
Qa=s.diff(Q,a);Qb=s.diff(Q,b);Qq=s.diff(Q,q)
aq=(-a*Qq-3*q*q*Qb)/J
bq=(b*Qq+3*q*q*Qa)/J
def par(f,p):
    P=s.diff(Q,p)
    return s.diff(f,p)-a*P*s.diff(f,a)/J+b*P*s.diff(f,b)/J
def dq(f):return s.diff(f,q)+aq*s.diff(f,a)+bq*s.diff(f,b)
def A0(f):return -c*par(f,c)/3-2*d*par(f,d)/3-e*par(f,e)/6
def B0(f):return -c*par(f,c)/3-d*par(f,d)/6-e*par(f,e)/6
def T0(f):return -c*par(f,c)/3-d*par(f,d)/6-2*e*par(f,e)/3
def zero_on_curve(expr):
    n=s.together(expr).as_numer_denom()[0]
    # Dense chart q*a≠0; no coordinate coefficient is fixed or discarded.
    return s.factor(n.subs(b,q**3/a).subs(
       c,(-a*a-q**6/a**2-d*a*q-e*q-1)/q**2))==0
zeta=b/q;xi=a/q
f1=a*q/(6*J)
f2=a*(2*c*q*q+d*a*q+e*q+3)/(18*J)
g1=-b*q/(6*J)
g2=-b*(2*c*q*q+4*d*a*q+e*q+3)/(18*J)
rows={
 'BE_CC':(par(par(zeta,c),c)+B0(par(xi,e))-par(xi,e)/6,f1),
 'BT_CE':(par(par(zeta,e),c)+B0(T0(xi)+xi/2),f2),
 'AE_CC':(par(par(xi,c),c)+A0(par(zeta,e))-par(zeta,e)/6,g1),
 'AT_CE':(par(par(xi,e),c)+A0(T0(zeta)+zeta/2),g2),
 'self_E_xi':(par(par(xi,e),e)-T0(par(xi,c))-par(xi,c)/6,a*q*q/(3*J)),
 'self_D_xi':(par(par(xi,d),d)-A0(par(xi,c))+s.Rational(5,6)*par(xi,c),-a*q*q/(6*J)),
}
checks={name:zero_on_curve(row-dq(potential))for name,(row,potential)in rows.items()}
assert all(checks.values()),checks
out={'checks':checks,'passed':True,'normalization':'A=B=T=1, raw zeta=b*dq/q, raw xi=a*dq/q',
 'fiber_potentials':{name:str(p)for name,(_,p)in rows.items()},
 'infinity_scope':'xi has residue d*(c-d²/4)/(4i); use xi_hat=xi-s*omega,s=d*(c-d²/4)/2,omega=q²dq/J',
 'certificate':False}
Path(__file__).with_name('normalized-toric-cross-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
