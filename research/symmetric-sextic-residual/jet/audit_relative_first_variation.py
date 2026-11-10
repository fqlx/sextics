from pathlib import Path
import sympy as S,json
from pathlib import Path
b,c,d,u,z,t=S.symbols('b c d u z t');ell=2*(1+z**3);K=2*(1+c**6);q=1+2*b-u;r=c*c+2*c*d-z*u
F0=b**6+d**6+ell*u**3+K;H=6*u+6*u**2+6*z*c**4*u+6*z**2*c*c*u**2+(q*q*r+2*q*r*r)/7
actual=2+b**6+2*c**6+d**6+30*u+30*u**2+2*u**3+30*z*c**4*u+30*z**2*c*c*u**2+2*z**3*u**3+S.Rational(5,7)*q*q*r+S.Rational(10,7)*q*r*r
assert S.expand(F0+5*H-actual)==0
P=b*d*(1-u)*(c*c-z*u);assert S.expand(P-b*d*(1-u)*(c*c-z*u))==0
A,B,C,D,X,Y,fb,hb,fu=S.symbols('A B C D X Y fb hb fu',nonzero=True);g=A+t*B;gu=C+t*D
src=2*b*d*(g*X-gu*Y)/g**3;src_slope=S.diff(src,t).subs(t,0);expect=2*b*d*((B*X-D*Y)/A**3-3*B*(A*X-C*Y)/A**4);assert S.cancel(src_slope-expect)==0
vec=S.symbols('vec');tangent=vec-(fb+t*hb)/(A+t*B)*fu;variation=S.diff(tangent,t).subs(t,0);assert S.cancel(variation-(-hb/A+fb*B/A**2)*fu)==0
# Along a moving zero F0+tH, u'(0)=-H/F0_u; therefore derivative of
# source-minus-tangent has the additional -H/F0_u * ∂u residual at t=0.
U,H0=S.symbols('U H0',nonzero=True);R0=S.Function('R0');T=S.symbols('T');path=U-T*H0/A;assert S.simplify(S.diff(R0(path),T).subs(T,0).doit()+H0/A*S.diff(R0(U),U))==0
print('PASS exact protected F=F0+5H, raw source P, source derivative, tangent derivative, and moving-fiber sign',flush=True)
