import sympy as s,time
from pathlib import Path
u,v,z=s.symbols('u v z');a,b=s.symbols('a b');W=v*v*z-u**3-a*u*z*z-b*z**3

def relation(F):
 H=s.expand(s.det(s.hessian(F,(u,v,z))));HH=s.expand(s.det(s.hessian(H,(u,v,z))));PF=s.Poly(F,u,v,z);PH=s.Poly(H,u,v,z);PP=s.Poly(HH,u,v,z)
 null=next(m for m,c in PH.terms()if PF.coeff_monomial(m)==0);beta=s.factor(PP.coeff_monomial(null)/PH.coeff_monomial(null));m=PF.monoms()[0];alpha=s.factor((PP.coeff_monomial(m)-beta*PH.coeff_monomial(m))/PF.coeff_monomial(m));print('ALPHA',alpha,'BETA',beta,flush=True)
 assert s.expand(HH-alpha*F-beta*H)==0
 return alpha,beta
al,be=relation(W);print('WEIERSTRASS_PASS',flush=True)
A,h,d,f,g,t=s.symbols('A h d f g t');F=A*u**3-h*v**3-t*z**3+d*u*u*v+g*u*v*z+f*u*z*z
I4=s.Rational(9,2)*A*g*h*t-d*f*f*h-g**4/48
I6=-A*f**3*h*h+s.Rational(5,8)*A*g**3*h*t+d*d*f*g*h*t+d*f*f*g*g*h/12+g**6/864+t*t*(-s.Rational(27,4)*A*A*h*h+d**3*h)
al2,be2=relation(F)
print('ALPHA_I4',s.factor(al2/I4**2));print('BETA_I6',s.factor(be2/I6));assert s.expand(al2-al.subs(a,I4))==0;assert s.expand(be2-be.subs(b,I6))==0;print('FULL_EXACT_INVARIANT_CHECK_PASS')
