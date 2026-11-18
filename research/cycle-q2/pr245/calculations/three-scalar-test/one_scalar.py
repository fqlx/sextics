import sympy as S
t,b,T=S.symbols("t b T", nonzero=True)
aa=2*t**4/b**5
bb=2*T**3/(t**5*b**8)
l,m,n,z=(2*b/t**2,2*t*b*T,2*t*b/T,2*t*b**4/T)
U=lambda q: -b*q.diff(b) - 3*T*q.diff(T)
V=lambda q: 5*t*q.diff(t) + 4*b*q.diff(b) + 19*T*q.diff(T)
C=l+m+n+z
e=V(C)
r=3*(m-n)/e
g=4*T/(3*t*b**2)
h1=16*b**2
# Factor cancellation in formal adjoint of (L-1)L and (L-1) C'.
mid=U(r*g) + r*V(r*g) - (h1-V(r*h1))/e
h=V(mid)
for point in [(1,1,1),(2,1,1)]:
 subs=dict(zip((t,b,T),point))
 print(point,"E", e.subs(subs),"r",r.subs(subs),"mid",mid.subs(subs),"h",h.subs(subs))
assert S.simplify(U(C)+r*V(C)+C)==0
assert S.simplify(U(aa)+r*V(aa)-5*aa)==0
assert S.simplify(U(bb)+r*V(bb)+bb)==0
