"""Exact quartic-normal source interface, not a constructed coefficient field."""
import sympy as s
u,v,z,a,b=s.symbols('u v z a b')
S=1+z**6+a**6+b**6+u*z/2+u*a*b/3
T=u**3*z*a*b/2
R=u**6
G=v**4+S*v**2+T*v+R
variables=[u,z,a,b]
E=[q/6 for q in variables]
apply=lambda W,P:sum(w*s.diff(P,q)for w,q in zip(W,variables))
K=1+u*z/3+u*a*b/6
assert s.expand(apply(E,S)-S+K)==0
assert s.expand(apply(E,T)-T)==0
assert s.expand(apply(E,R)-R)==0
assert sum(s.diff(w,q)for w,q in zip(E,variables))==s.Rational(2,3)
# Abstract directional jets and base divergence bind the source identity.
WS,WT,WR,divW=s.symbols('WS WT WR divW')
WG=WS*v**2+WT*v+WR
assert s.expand((-WG+G*divW).subs({WS:S,WT:T,WR:R,divW:1})-v**4)==0
# The full polynomial model has a nonnormal boundary candidate in codimension one.
assert all(s.diff(G,q).subs({u:0,v:0})==0 for q in [u,v,z,a,b])
q=s.symbols('q')
leading=s.expand(G.subs(v,q*u**3)/u**6)
S0=S.subs(u,0)
assert s.expand(leading.subs(u,0)-(S0*q**2+z*a*b*q/2+1))==0
print('Verified exact coefficient-field sufficient identity -W(G)+G divW=v^4.')
print('Verified Euler gaps K=1+uz/3+uab/6 and div gap 1/3.')
print('Verified singular boundary u=v=0 and normalized leading branch equation.')
