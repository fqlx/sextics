import sympy as s
x=s.symbols('x');J=s.Function('J')(x);F=s.Function('F')(x)
RY=lambda v:s.diff(v/s.diff(J,x),x)
for n in range(1,5):
 rhs=-s.diff(F/(n*s.diff(J,x)*J**n),x)+RY(F)/(n*J**n)
 assert s.cancel(rhs-F/J**(n+1))==0
# Complete finite reduction for one arbitrary coefficient at each pole order.
for k in range(1,5):
 rem=F;S=0
 for j in range(k):
  S-=s.Rational(s.factorial(k-j-1),s.factorial(k))*rem/(s.diff(J,x)*J**(k-j))
  rem=RY(rem)
 rhs=s.diff(S,x)+rem/(s.factorial(k)*J)
 assert s.cancel(rhs-F/J**(k+1))==0
# Universal fourth derivative expansion at an ordinary J divisor.
g=s.Function('g')(x)
expr=s.diff(g/J,x,4)
num=s.expand(expr*J**5)
# Terms of J degree zero are exactly the pole-five coefficient.
# Substitute only J, retaining its derivative jets as independent symbols.
j0,j1,j2,j3,j4=s.symbols('j0:5');g0,g1,g2,g3,g4=s.symbols('g0:5')
sub={s.diff(J,x,i):v for i,v in enumerate((j0,j1,j2,j3,j4))}
sub.update({s.diff(g,x,i):v for i,v in enumerate((g0,g1,g2,g3,g4))})
jet=s.expand(num.xreplace(sub))
assert s.cancel(jet.subs(j0,0)-24*g0*j1**4)==0
print('Exact joint J-pole homotopies and fourth-order leading coefficient passed.')
