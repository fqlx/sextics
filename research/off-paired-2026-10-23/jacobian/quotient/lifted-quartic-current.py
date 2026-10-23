"""Actual rational current for the exact quartic source, with explicit defect.

This is not a certificate: the nonzero pole-one correction must be canceled.
"""
import sympy as s
u,v,z,a,b=s.symbols('u v z a b')
rr=a*b; ss=a**6+b**6; AA=a**6-b**6
S=1+z**6+ss+u*z/2+u*rr/3
T=u**3*z*rr/2
R=u**6
G=v**4+S*v**2+T*v+R
K0=S/3+u*z/36-u*rr/27
base=[u,z,a,b]
W=[-u/18,s.S(0),a*(K0-b**6)/(6*AA),b*(a**6-K0)/(6*AA)]
apply=lambda P:sum(w*s.diff(P,q)for w,q in zip(W,base))
for P,target in [(S,S/3),(T,0),(R,-R/3)]:
 assert s.cancel(apply(P)-target)==0
Nv=-v/3
NG=apply(G)+Nv*s.diff(G,v)
assert s.cancel(NG+G/3+v**4)==0
h=s.Rational(4,9)-(ss*K0-2*rr**6)/AA**2
Div=sum(s.diff(w,q)for w,q in zip(W,base))+s.diff(Nv,v)
assert s.cancel(Div+s.Rational(1,3)-h)==0
assert s.cancel(G*Div-NG-v**4-G*h)==0
print('Verified actual rational current N(G)=-G/3-v^4, div N=-1/3+h.')
print('Verified exact source plus correction G divN-N(G)=v^4+G h.')
print('Defect h at u=v=z=a=1,b=2:',s.factor(h.subs({u:1,v:1,z:1,a:1,b:2})))

p,H,C,Kb=s.symbols('p H C Kb')
f=(H+C*p)**2-4*p**6
# On F=0, ss=-(H+Cp), K0=ss/3+Kb+2up/27.
Kp=-(H+C*p)/3+Kb+2*u*p/27
hn=s.expand(s.Rational(4,9)*f-(-(H+C*p))*Kp+2*p**6)
# h dp/Z = 1/36 d(p/Z) - (H/12+Kb) nabla_H omega0
#                              - (C/9+2u/27) nabla_C omega0.
exact_num=(f-p*s.diff(f,p)/2)/36
rest_num=(H+C*p)*(H/12+Kb+(C/9+2*u/27)*p)
assert s.expand(hn-exact_num-rest_num)==0
print('Verified endpoint Hermite reduction of remaining pole-one correction.')
