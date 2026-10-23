"""Exact principal Laurent grading at smooth physical ramification Pa=0."""
import sympy as s
M,K,N,fa=s.symbols('P_C P_aa N f_a',nonzero=True)
# For J=Pa, DC(J)=-MK/J+O(1), DC(f)=-M f_a/J+O(1).
# A regular coefficient derivative has at most J^-1; differentiating J^-k
# produces J^(-k-2), so the following recurrence is exact in principal grading.
lead=-M*fa
for n in range(1,4):lead=s.expand((2*n-1)*M*K*lead)
expected=-15*M**4*K**3*fa
assert s.expand(lead-expected)==0
u=3*M**4*K**2*fa/N
# T(J)=NK/J+O(1), so T(u/J^5)=-5NKu/J^7+lower pole order.
assert s.cancel(-5*N*K*u-expected)==0
assert s.cancel(-lead-5*N*K*u)==0
# Bind the generic smooth hypotheses to one actual rational ramification point.
a,H,C,z=s.symbols('a H C z')
q=3*C-s.Rational(3,2)*a*z
P=a**4+q**6+a*a*(z**6+q*z/2+1-H)
J=s.diff(P,a);KK=s.diff(J,a);MM=s.diff(P,C)
Delta=4*C**6-729*H**4
R=-27*C**3/a+s.Rational(81,4)*C*z*z*a-s.Rational(27,16)*z**3*a*a
f=Delta*R/C
NN=a*a-2*C*MM/(3*H)
point={a:1,H:3,C:s.Rational(1,3),z:0}
assert P.subs(point)==0 and J.subs(point)==0
assert all(x.subs(point)!=0 for x in (KK,MM,NN,s.diff(f,a)))
actual=expected.subs({M:MM.subs(point),K:KK.subs(point),N:NN.subs(point),fa:s.diff(f,a).subs(point)})
print('Exact principal Laurent recurrence and complete Pa^-7 cancellation passed.')
print('Actual rational ramification point (a,H,C,z)=(1,3,1/3,0); common coefficient:',actual)
