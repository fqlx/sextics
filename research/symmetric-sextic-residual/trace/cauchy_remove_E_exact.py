"""Exact cubic algebra identity for a source-matched interpolant with E pole removed."""
import sympy as s
v,u,A,B,C,p,q,r,J,ell,G,ab,bb=s.symbols('v u A B C p q r J ell G ab bb', nonzero=True)
g=lambda x:A*x*x+B*x+C
P=lambda x:p*x*x+q*x+r
Pp=lambda x:2*p*x+q
gp=lambda x:2*A*x+B
N=s.expand(g(v)*Pp(v)-gp(v)*P(v)); Na=s.expand(g(u)*Pp(v)-gp(u)*P(v));Q=s.cancel((N-Na)/(v-u));assert s.denom(Q)==1
E=2*r+q*v;vstar=-2*r/q
alpha=s.factor(-N.subs(v,vstar)/((u-vstar)*Q.subs(v,vstar)))
R=s.factor(N+alpha*(u-v)*Q); assert s.factor(R.subs(v,vstar))==0
L=s.cancel(R/E);assert s.denom(L).free_symbols.isdisjoint({v})
Lpoly=s.Poly(L,v);assert Lpoly.degree()<=1
l0=s.factor(Lpoly.nth(0));l1=s.factor(Lpoly.nth(1))
F0=ell*u**3+J;gu=3*ell*u*u
# beta=ab/v+bb/v²: reduction of L beta in the auxiliary cubic
T0=l1*ab;T1=-ell*l1*bb/J;T2=-ell*(l0*ab+l1*bb*0)/J
# Correct multiplication: 1/v=-ell*v²/J, 1/v²=-ell*v/J
T0=l1*ab; T1=-ell*(l0*bb)/J; T2=-ell*(l0*ab+l1*bb)/J
current=s.factor(3*J/G**3*(gu*(T0+T1*u+T2*u*u)-3*F0*(T1+u*T2)))
aux=ell*v**3+J; w=3*J*F0*L/(G**3*(u-v)); raw=s.cancel(w*(ab/v+bb/v**2));num,den=s.fraction(raw);res=s.rem(num*s.invert(den,aux,v),aux,v); trace=s.factor(sum(s.rem(res*v**j,aux,v).coeff(v,j) for j in range(3)))
assert s.factor(trace-current)==0
assert s.factor(L.subs(v,u)-N.subs(v,u)/E.subs(v,u))==0
compact=9*J*ell*N.subs(v,u)*(bb+ab*u)/(G**3*E.subs(v,u))
assert s.factor(current-compact)==0
print('PASS: current collapses to 3J Nt(u)/(G³ E(u)) times bare-trace numerator')
print('alpha=',s.factor(alpha));print('l0=',l0);print('l1=',l1);print('PASS: E cancels and compact interpolated current equals exact cubic trace')
