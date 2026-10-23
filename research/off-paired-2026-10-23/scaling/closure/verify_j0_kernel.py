"""Exact identities for the j=0 quotient and source-weighted beta correspondence.

This does not verify a primitive or certificate.
"""
import sympy as s

w,T,q,z,delta,L,p,Q=s.symbols('w T q z delta L p Q')
b=3*z*z/4
R=2*T+w**3-b
# Base equations: T^2+(w^3-b)T+delta^2=0, q^2=T*w.
def reduce_base(expr):
    n,d=s.fraction(s.cancel(expr))
    n=s.rem(n,s.Poly(q*q-T*w,q),q)
    n=s.rem(n,s.Poly(T*T+(w**3-b)*T+delta**2,T),T)
    return s.factor(n)

qp=delta*w/q
Tp=delta**2/T
assert reduce_base(T+Tp-(b-w**3))==0
assert reduce_base(T-Tp-R)==0
assert reduce_base(qp**2-Tp*w)==0
Qp=q+qp;Qm=q-qp
assert reduce_base(Qp**2-w*(b+2*delta-w**3))==0
assert reduce_base(Qm**2-w*(b-2*delta-w**3))==0
assert reduce_base(Qp*Qm-w*R)==0
C=z*T/2+q/3;Cp=z*Tp/2+qp/3
A=z*(b-w**3)/2+Qp/3
P=z*z*delta*delta/4+z*delta*Qp/6+delta*w/9
assert reduce_base(C+Cp-A)==0
assert reduce_base(C*Cp-P)==0
assert reduce_base(w*(Cp-C)/(6*R)+z*w/12+w*w/(18*Qp))==0

# The endpoint norm is an identity in the symmetric functions of C,C'.
c1,c2,A0,P0,d,e=s.symbols('c1 c2 A0 P0 d e')
norm=((L+d*c1)**2-e)*((L+d*c2)**2-e)
norm_s=(L*L+d*L*(c1+c2)+d*d*c1*c2+e)**2-e*(2*L+d*(c1+c2))**2
assert s.expand(norm-norm_s)==0
k=s.symbols('k')
moddiff=c2**3*(L+k*c1)**2-c1**3*(L+k*c2)**2
modfactor=(c2-c1)*((L*(c1+c2)+k*c1*c2)**2-L*L*c1*c2)
assert s.expand(moddiff-modfactor)==0

# Variable-j quotient's rational 3-torsion section.
alpha,X=s.symbols('alpha X')
AW=-3*(2*alpha+5);BW=alpha*alpha+14*alpha+22
assert s.expand((alpha-2)**2-(3**3+AW*3+BW))==0
psi3=3*X**4+6*AW*X*X+12*BW*X-AW*AW
assert s.expand(psi3.subs(X,3))==0
print('PASS: base involutions, both j0 quotients, weighted density, full endpoint norm, modulus difference, 3-torsion')
