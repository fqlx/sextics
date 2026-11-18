"""Independent exact checks for the rational reduction to one holomorphic form.

Examine the normalized plane sextic at F=0; taking C from this equation
makes the tests ordinary equalities in Q(A,B,X,Y).  The base identities
are checked separately as Laurent identities in Q(t,b,T).
"""
from sympy import Matrix, cancel, diff, symbols

t, b, T, I, J, x, y = symbols('t b T I J x y', nonzero=True)
def zero(q):
    assert cancel(q) == 0, q

A, B, C = 2*t**4/b**5, 2*T**3/(t**5*b**8), 2*b/t**2 + 2*t*b*(T+(1+b**3)/T)
m=t**2/(2*b)
Ival=x/t
yval=t*y/b
JD=T+(1+b**3)/T+Ival/(2*b)+Ival**6*T**3/b**9
f=yval**6+1+JD*t**3 +yval*(Ival*t**2+t)/2
zero(f-m*(A*y**6+B*x**6+x*y+x+y+C))
fy=6*yval**5+(Ival*t**2+t)/2
zero(fy-t*(6*A*y**5+x+1)/2)
W=Ival**2/(6*b**5)+2*Ival/(b*T)
g2=4*T/(3*t*b**2)
g1=16*b**2
zero(t**6*(2/t)*m**-2*W/t*(t*b*T) - (g2*x*x+g1*x))
P=I**6*T**4+b**9*T**2+(I*b**8/2-J*b**9)*T+b**12+b**9
j=T+(1+b**3)/T+I/(2*b)+I**6*T**3/b**9
zero(diff(j,T) - diff(P,T).subs(J,j)/(b**9*T))
print("Change of equation, normal derivative, both source coefficients, and J_D Jacobian pass.")

a,c,X,Y=symbols('A B X Y',nonzero=True)
const=-(a*Y**6+c*X**6+X*Y+X+Y)
fy=6*a*Y**5+X+1
rho=1/fy
S=lambda q: -diff(q,Y)/fy
L=lambda q: 5*a*diff(q,a)-c*diff(q,c)-(Y+X/fy)*diff(q,Y)
for f in [a,c,X,Y]:
    zero(S(L(f))-L(S(f))+S(f))
zero(L(const)+const)
zero(S(const)-1)
zero(S(X*rho)-L(rho))
zero(S(X*X*rho)-L(X*rho))
zero(S(S(X*X*rho))-(L(L(rho))-L(rho)))
zero(S(S(X*rho))-(L(S(rho))-S(rho)))
print("Both literal fixed-X density transports and commutator pass.")

V=lambda q: 5*t*diff(q,t)+4*b*diff(q,b)+19*T*diff(q,T)
U=lambda q: -b*diff(q,b)-3*T*diff(q,T)
E=V(C)
r=6*t*b*(T-1/T)/E
for q,expectedU in [(A,5*A),(B,-B),(C,-C)]:
    zero(U(q)+r*V(q)-expectedU)
zero(V(A))
zero(V(B))
zero(U(g2)+g2)
zero(U(g1)+2*g1)
print("Base lifts of the two derivations pass.")

# Check orientation through dI,dJ,dτ,db against dI,dτ,db,dT.
vol=Matrix([[1,0,0,0],[diff(j,I),0,diff(j,b),diff(j,T)],
            [0,1,0,0],[0,0,1,0]])
zero(vol.det()-diff(j,T))
nu=Matrix([[1/t,0,0],[0,1/b,0],[0,0,1/T]])
zero(nu.det()-1/(t*b*T))
z,d,alpha=symbols('z d a',nonzero=True)
sub={t:z**5/alpha,b:z**4/alpha,T:d*z**19/alpha**5}
s=z**2
for f,val in [(A,2*alpha),(B,2*d**3/alpha**2),
               (C,2*alpha/s**3+2*d*s**14/alpha**7+2*alpha**3/(d*s**5)+2*s/d),
               (g2,4*d*s**3/(3*alpha**2)),(g1,16*s**4/alpha**2)]:
    zero(f.subs(sub,simultaneous=True)-val)
print("Orientation, sign-quotient coordinates and degree-19 projection pass.")
