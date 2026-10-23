import sympy as s
H,C,z,a=s.symbols('H C z a')
q=3*C-s.Rational(3,2)*a*z
P=a**4+q**6+a**2*(z**6+q*z/2+1-H)
Pa=s.diff(P,a)
def D(v,b):
    return s.diff(v,b)-s.diff(P,b)*s.diff(v,a)/Pa
for b in (H,C,z):assert s.cancel(D(P,b))==0
for b,c in ((H,C),(H,z),(C,z)):
    assert s.cancel(D(D(a,b),c)-D(D(a,c),b))==0
phi=q**3/Pa
expected=((2*a*q**3+3*a**2*q**2*s.diff(q,a))*Pa-a**2*q**3*s.diff(Pa,a))/Pa**3
assert s.cancel(D(phi,H)-expected)==0
# Abstract commuting coefficient jets, to verify the complete horizontal current.
f0,f1,f2,f3,f4,U,UH,UC,WZ=s.symbols('f0 f1 f2 f3 f4 U UH UC WZ')
Delta=4*C**6-729*H**4
cs=[-55*C**2/Delta,-309*C**3/Delta,-(271*C**6-1458*H**4)/(C**2*Delta),-2*(32*C**6+729*H**4)/(C*Delta)]
def DC(v):
    return s.diff(v,C)+sum(s.diff(v,x)*y for x,y in zip((f0,f1,f2,f3,U),(f1,f2,f3,f4,UC)))
NC=s.zeros(4)
for j in range(3):NC[j+1,j]=1
for j in range(4):NC[j,3]=cs[j]
e=-2*C/(3*H)
NH=e*NC-s.diag(*[(2+2*j)/(3*H) for j in range(4)])
u=s.Matrix([U,0,0,0])
t=s.Matrix([-f3-DC(DC(cs[3]*f0))+DC(cs[2]*f0)-cs[1]*f0,
            f2+DC(cs[3]*f0)-cs[2]*f0,-f1-cs[3]*f0,f0])
v=t-e*u
r=s.Matrix([UH,0,0,0])+NH*u+v.applyfunc(DC)+NC*v+s.Matrix([WZ,0,0,0])
Lstar=f4+DC(DC(DC(cs[3]*f0)))-DC(DC(cs[2]*f0))+DC(cs[1]*f0)-cs[0]*f0
wanted=s.Matrix([-Lstar+UH+2*C*UC/(3*H)+WZ,0,0,0])
assert (r-wanted).applyfunc(s.cancel)==s.zeros(4,1)
# Both source conventions, with all actual physical derivatives.
assert s.cancel(-C*D(phi,C)/(9*H)-(-D(phi,H)/6-C*D(phi,C)/(9*H))-D(phi,H)/6)==0
print('Physical derivations, corrected phi_H, and all four horizontal reconstruction rows passed.')
# Parent-derived denominator-free Euler form of the adjoint operator.
g=s.Function('g')(C)
f=C**2*Delta*g
Lf=s.diff(f,C,4)+s.diff(cs[3]*f,C,3)-s.diff(cs[2]*f,C,2)+s.diff(cs[1]*f,C)-cs[0]*f
def theta(v):return C*s.diff(v,C)
def affine_theta(v,A,B):return A*theta(v)+B*v
def product_theta(v,factors):
    for A,B in factors:v=affine_theta(v,A,B)
    return v
rhs=C**4*product_theta(g,[(1,4),(1,4),(2,-1),(2,5)])-729*H**4/C**2*product_theta(g,[(1,0),(1,-1),(1,2),(1,3)])
assert s.cancel(Lf-rhs)==0
print('Denominator-free Euler adjoint identity passed.')
