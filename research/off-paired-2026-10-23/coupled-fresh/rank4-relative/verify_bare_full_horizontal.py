"""Exact actual source map and complete bare four-row current checks."""
import sympy as s
x,y,z,a,C=s.symbols('x y z a C')
q=3*C-s.Rational(3,2)*a*z
H=a*a+q**6/(a*a)+z**6+q*z/2+1
h=s.diff(H,C);Ha=s.diff(H,a);Hz=s.diff(H,z);N=3*H-2*C*h
Cxy=x**3*z/2+x*y/3
Hxy=1+x**6+y**6+z**6+x*y*z/2
sub={a:x**3,C:Cxy}
assert s.cancel(q.subs(sub)-x*y)==0
assert s.cancel(H.subs(sub)-Hxy)==0
jac=s.det(s.Matrix([[s.diff(f,t) for t in (x,y,z)]for f in (x**3,Cxy,z)]))
assert s.cancel(jac-x**3)==0
assert s.cancel((q**3/a**2).subs(sub)*jac-y**3)==0
# Actual Piola matrix, retaining both C derivative terms.
M=s.Matrix([[s.diff(f,t) for t in (x,y,z)]for f in (x**3,Cxy,z)])
Va,VC,Vz=s.symbols('Va VC Vz')
claimed=s.Matrix([x*Va/3,3*x*x*VC-s.diff(Cxy,x)*Va-3*x*x*s.diff(Cxy,z)*Vz,x**3*Vz])
assert (claimed-jac*M.inv()*s.Matrix([Va,VC,Vz])).applyfunc(s.cancel)==s.zeros(3,1)
# Generic scalar current reconstruction in any actual bare cyclic companion.
cc=s.symbols('cc')
d=[s.Function(f'd{j}')(cc)for j in range(4)]
g=s.Function('G')(cc);U=s.Function('U')(cc);W=s.Function('W')(cc)
HA=s.Function('Ha')(cc);HZ=s.Function('Hz')(cc);NN=s.Function('N')(cc)
Ua,Wz=s.symbols('Ua Wz')
P=HA*U+HZ*W
v=s.Matrix([-s.diff(g,cc,3)-s.diff(d[3]*g,cc,2)+s.diff(d[2]*g,cc)-d[1]*g+2*cc*P/NN,
 s.diff(g,cc,2)+s.diff(d[3]*g,cc)-d[2]*g,-s.diff(g,cc)-d[3]*g,g])
MC=s.zeros(4)
for j in range(3):MC[j+1,j]=1
for j in range(4):MC[j,3]=d[j]
r=v.diff(cc)+MC*v+s.Matrix([Ua+Wz-2*P/NN,-2*cc*P/NN,0,0])
Lstar=s.diff(g,cc,4)+s.diff(d[3]*g,cc,3)-s.diff(d[2]*g,cc,2)+s.diff(d[1]*g,cc)-d[0]*g
wanted=s.Matrix([-Lstar+Ua+Wz+2*cc*s.diff(P/NN,cc),0,0,0])
assert (r-wanted).applyfunc(s.cancel)==s.zeros(4,1)
# Exact elementary source current: delta(C F t0) plus residual -C deltaF.
FF=s.Function('F')(cc)
assert s.expand(s.diff(cc*FF,cc)-cc*s.diff(FF,cc)-FF)==0
print('Actual physical source map, Piola transformation, and all four bare-horizontal rows passed.')
