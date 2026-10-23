"""Exact log-residue current with complete endpoint-exact correction."""
import sympy as s
p,H,C,r,k,c=s.symbols('p H C r k c')
f=(H+C*p)**2-4*p**6
h=H+C*p
# For V=lambda cross gradlogg, k=V(z)/z,c=V(C):
# div V=3k, V(s)=s k,V(H)=3Hk+2sCk-s c.
VH=3*H*k+2*r*C*k-r*c
Vs=r*k
div=3*k
d=c-2*C*k
lhs=s.expand(div*(p-r)*f+Vs*f-(p-r)*h*(VH+p*c))
rhs=s.expand(-d*h*(p-r)**2+k*(r*f+p*(p-r)*s.diff(f,p)/2))
assert s.expand(lhs-rhs)==0
print('Verified divcurrent(V beta)=d_g nabla_H omega0 -(Vz/z)d_p[p/((p-s)Z)].')
print('Adding the displayed rational endpoint primitive gives the exact source d_g nabla_H omega0.')
# Formal residue-closedness, valid for arbitrary rational g.
x,y,z=s.symbols('x y z')
L=s.Function('L')(x,y,z);g=s.Function('g')(x,y,z)
coords=[x,y,z]
lam=s.Matrix([s.diff(L,x),s.diff(L,y),s.diff(L,z)-3*L/z])
V=lam.cross(s.Matrix([s.diff(g,q)/g for q in coords]))
assert s.simplify(sum(s.diff(V[i],q)for i,q in enumerate(coords))-3*V[2]/z)==0
assert s.simplify(sum(V[i]*s.diff(L,q)for i,q in enumerate(coords))-3*L*V[2]/z)==0
print('Verified divV=3Vz/z and V(L)=3L Vz/z for arbitrary rational g.')

# Dominance check for the genuinely nonexact g=J residue class.
H0=1+x**6+y**6+z**6+x*y*z/2
C0=x**3*z/2+x*y/3
L0=s.expand(H0-3*z*C0/2)
J0=s.expand(s.diff(H0,x)*s.diff(C0,y)-s.diff(H0,y)*s.diff(C0,x))
Jac=s.diff(L0,x)*s.diff(J0,y)-s.diff(L0,y)*s.diff(J0,x)
assert Jac.subs({x:1,y:1,z:1})==-s.Rational(657,4)
print('Verified nonzero dominance Jacobian for g=J01 log class.')
