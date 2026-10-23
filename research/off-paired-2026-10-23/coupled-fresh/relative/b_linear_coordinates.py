"""Exact coordinate and actual-source checks, no certificate claim."""
import sympy as s
z,U,B,C,p=s.symbols('z U B C p')
L=2+3*z*U
K=(6*B-3*U)/L
Q=C-z**-2-U**6
t=K**6/Q
H=1+z**2+t
rho=-1/(3*z**2*L*Q)
# Original actual density in (z,U,K,t), with B,C replacing K,t.
jac=s.det(s.Matrix([[s.diff(K,B),s.diff(K,C)], [s.diff(t,B),s.diff(t,C)]]))
assert s.cancel(jac/(18*t*z**2)-rho)==0
assert s.diff(rho,B)==0
assert s.cancel(U/2+K/3+z*U*K/2-B)==0
assert s.cancel(z**-2+U**6+K**6/t-C)==0
# The fixed-H lift of coefficient d/dB has divergence zero in actual density.
v=s.cancel(s.diff(H,B)*Q/(H-(1+z**2)))
assert s.cancel(s.diff(H,B)+v*s.diff(H,C))==0
assert s.cancel(s.diff(rho,B)+s.diff(rho*v,C))==0
# Full physical derivative of universal q=p_B=-p/g, retaining all H derivatives.
h,b,c=s.symbols('h b c')
f=c*p**3+b*p+h
g=b+3*c*p**2
q=-p/g
R=b*p/g**3
def d(q,var):
    return s.diff(q,var)-s.diff(q,p)*s.diff(f,var)/g
def rem(q):
    num,den=s.fraction(s.cancel(q))
    return s.rem(num,f,p)
assert rem(d(q,b)-2*R)==0
assert rem(d(q,h)+q/(3*h)+4*b*R/(3*h))==0
assert rem(d(q,c)+2*q/(3*c)+2*b*R/(3*c))==0
print('9 exact coordinate/source identities passed')
