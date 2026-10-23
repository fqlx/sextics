"""Source-guided odd aq variation at the symmetric canonical quadric."""
import sympy as s,json
from pathlib import Path
A,B,C,E,a,b,q,rho,lam=s.symbols('A B C E a b q rho lam',nonzero=True)
J=2*A*a*a-2*B*b*b
F=lam*C/(B*rho*(b+rho))
m0=F*(a*a*(-2*rho*q+3*b*E/(2*C))/(J*(b+rho))-E/(4*A*C))
odd=s.cancel((m0-m0.subs(b,-b))/2)
JD=a*q*(1-4*(A*a*a+B*b*b)/J)
inf=3*lam*E/rho*q*q*JD/J**2
# On ab=q³, a*q³=a²*b.
inf=s.cancel(inf.subs(q**3,a*b))
print('oddpart',s.factor(odd),flush=True)
print('infty',s.factor(inf),flush=True)
comb=s.factor(odd+inf)
print('combined',comb,flush=True)
# Numerator against holomorphic eta_b=b/J.
ratio=s.factor(comb/(b/J))
print('ratio',ratio,flush=True)
# The centered quadric identity is A a²+B b²+Cq²+Eq+E²/(4C)−B rho²=0.
num,den=s.fraction(s.cancel(ratio));pp=s.Poly(A*a*a+B*b*b+C*q*q+E*q+E*E/(4*C)-B*rho*rho,q)
rem=s.rem(num,pp,q).as_expr()
print('reduced',s.factor(rem),flush=True)
Path(__file__).with_name('odd-D-comparison.json').write_text(json.dumps({'odd_compact_representative':str(comb),'ratio_to_eta_b':str(ratio),'source_match':'not yet compact-reduced; no claimed proportionality'},indent=2)+'\n')
