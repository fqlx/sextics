"""Exact source-driven genuine horizontal current identity."""
import sympy as s
q,a,z,K,M,E,F,J5,L=s.symbols('q a z K M E F J5 L')
Res=F**2-K*E*F+M*E**2
w1=(-F*(K**2-M)+K*M*E)/(6*a*a*Res)
w0=M*(E*M-K*F)/(6*a*a*Res)
Wb=w1*q+w0
Q=q*q+K*q+M
V=(K-q)/(6*a*a)-E*w1-J5*Wb
Hz=J5*Q+E*q+F
Ha=L*Hz-Q/(9*a*a)
U=-9*a*a*V; W=Wb+9*a*a*L*V
assert s.cancel(Ha*U+Hz*W+q**3/(6*a*a))==0
# Bind the generic quadratic and linear remainders to the actual H(a,C,z).
kk=3*a*z+12*z**5; mm=-18*a**3+54*a*z**6
ll=z/a+2*q/(9*a*a)
haa=2*a-2*q**6/a**3-9*z*q**5/a**2-s.Rational(3,4)*z*z
hzz=6*z**5+q/2-s.Rational(3,4)*a*z-9*q**5/a
ee=s.Rational(1,2)-9*(kk**4-3*kk*kk*mm+mm*mm)/a
ff=6*z**5-s.Rational(3,4)*a*z-9*(kk**3*mm-2*kk*mm*mm)/a
jj=-9/a*(q**3-kk*q*q+(kk*kk-mm)*q-kk**3+2*kk*mm)
qq=q*q+kk*q+mm
assert s.cancel(haa-ll*hzz+qq/(9*a*a))==0
assert s.cancel(hzz-jj*qq-ee*q-ff)==0
rr=s.cancel((F*F-K*E*F+M*E*E).subs({K:kk,M:mm,E:ee,F:ff}))
assert rr.subs({a:1,z:0})!=0
print('Exact generic source Bezout, physical polynomial binding, and nonzero resultant passed.')
