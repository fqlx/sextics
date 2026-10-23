"""Exact source-carrying moving-pole current and its remaining defect."""
import sympy as s
x,y,z=s.symbols('x y z')
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3
r=-s.Rational(3,2)*z
L=s.expand(H+r*C)
J=s.expand(s.diff(H,x)*s.diff(C,y)-s.diff(H,y)*s.diff(C,x))
A=y**3
W=[A*s.diff(L,y)/(6*J),-A*s.diff(L,x)/(6*J),s.S(0)]
assert s.cancel(sum(Wi*s.diff(C,u)for Wi,u in zip(W,[x,y,z]))+A/6)==0
assert s.cancel(sum(Wi*s.diff(L,u)for Wi,u in zip(W,[x,y,z])))==0
F=s.expand(L**2-4*r**6)
assert s.cancel(sum(Wi*s.diff(F,u)for Wi,u in zip(W,[x,y,z])))==0
D=s.factor(sum(s.diff(Wi,u)for Wi,u in zip(W,[x,y,z])))
expected=(A*(s.diff(L,x)*s.diff(J,y)-s.diff(L,y)*s.diff(J,x))-s.diff(A,y)*s.diff(L,x)*J)/(6*J**2)
assert s.cancel(D-expected)==0
assert s.cancel(D.subs({x:1,y:1,z:1}))==-s.Rational(97,1014)
print('Verified W(L)=W(s)=W(F_s)=0, W(C)=-A/6.')
print('Remaining beta-row defect is div(W)=',D)
print('At x=y=z=1:',D.subs({x:1,y:1,z:1}))
# Independent formal weighted-curl identity: no compact connection assumed.
coords=[x,y,z]
f=s.Function('F')(x,y,z)
AA=[s.Function('A'+str(i))(x,y,z)for i in range(3)]
V=[]
for i,j,k in [(0,1,2),(1,2,0),(2,0,1)]:
    V.append(s.diff(AA[k],coords[j])-s.diff(AA[j],coords[k])-(s.diff(f,coords[j])*AA[k]-s.diff(f,coords[k])*AA[j])/(2*f))
assert s.simplify(sum(s.diff(Vi,u)-Vi*s.diff(f,u)/(2*f)for Vi,u in zip(V,coords)))==0
print('Verified formal weighted-curl residue identity for arbitrary F and A_i.')
