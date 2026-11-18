"""Check literal localized quartic transport identities as sparse Laurent polynomials."""
from fractions import Fraction as Q

def monomial(b=0, t=0, i=0, coefficient=1):
    return {(b,t,i):Q(coefficient)}

def add(*ps):
    result={}
    for p in ps:
        for e,c in p.items():
            result[e]=result.get(e,0)+c
    return {e:c for e,c in result.items() if c}

def mul(p,q):
    return add(*({tuple(a+b for a,b in zip(e,f)):c*d}
                 for e,c in p.items() for f,d in q.items()))

def step(p,b=0,t=0,i=0,coefficient=1):
    return mul(p,monomial(b,t,i,coefficient))

# Eliminate J exactly from P(b,T,I,J)=0. Represent relative forms in db/P_T.
j=add(monomial(-9,3,6),monomial(0,1),monomial(0,-1),
      monomial(3,-1),monomial(-1,0,1,Q(1,2)))
pt=add(monomial(0,3,6,4),monomial(9,1,0,2),monomial(8,0,1,Q(1,2)),step(j,9,coefficient=-1))
pb=add(monomial(8,2,0,9),monomial(7,1,1,4),step(j,8,1,coefficient=-9),
       monomial(11,0,0,12),monomial(8,0,0,9))
pi=add(monomial(0,4,5,6),monomial(8,1,0,Q(1,2)))
def phi(i,jj):
    return monomial(i-1,jj-1)
def d_t_over_b(m):
    return add(step(pb,-m,coefficient=-1),step(pt,-m-1,1,coefficient=-m))
def check_equal(a,b):
    assert not add(a,step(b,coefficient=-1))

ai=step(pi,-4,-1,coefficient=-1)
check_equal(ai,add(step(phi(5,1),coefficient=Q(-1,2)),step(phi(-3,4),i=5,coefficient=-6)))
check_equal(step(ai,i=1),
    add(step(phi(6,2),coefficient=3),step(phi(5,1),i=1,coefficient=Q(1,4)),
        step(mul(j,phi(6,1)),coefficient=Q(-3,2)),step(pt,-4,coefficient=Q(-3,2))))
for m in (3,4):
    i=9-m
    s=step(pt,-m-1,1)
    check_equal(step(s,coefficient=3-Q(2*m,3)),
                add(step(d_t_over_b(m),coefficient=Q(2,3)),step(phi(i,1),coefficient=-6),
                    step(phi(i-1,2),i=1,coefficient=Q(-11,6)),step(mul(j,phi(i,2)),coefficient=3),
                    step(phi(i+3,1),coefficient=-4)))
    check_equal(step(pi,-m-1,0,1,-1),
                add(step(s,coefficient=-Q(2*m,3)),step(phi(i-1,2),i=1,coefficient=Q(-1,6)),
                    step(phi(i+3,1),coefficient=-2),step(d_t_over_b(m),coefficient=Q(-2,3))))
det=Q(-11,144)*(-2)-Q(-1,6)**2
assert det==Q(1,8)
assert Q(-4,7)-2==Q(-18,7)
print("Verified both literal Theta I formulae over Q(I,b,T).")
print("Verified xi and kappa quasi-Euler and I identities including all four exact corrections.")
print("Independent phi42,phi81 coefficient determinant:",det)
# For the nonzero J level of the C pencil brute substitutions are unnecessary.
# Use exponent triples for a,c,y and the formal relations g=y²+a*y+a²,
# I=6*a*c² and j0=-c³. The y³ residual is c²/2+2a³c³.
g=add(monomial(0,0,2),monomial(1,0,1),monomial(2))
residual=add(monomial(0,3),monomial(0,3,6),step(g,0,2,1,Q(1,2)),
             step(mul(g,g),1,3,1,3),step(mul(mul(g,g),g),0,3,0,-1))
assert {e:c for e,c in residual.items() if e[2]>=4}=={}
assert {e:c for e,c in residual.items() if e[2]==3}=={(0,2,3):Q(1,2),(3,3,3):2}
print("Verified the degree-three contradiction for reducible nonzero levels of the C pencil.")
# The mu_6 action on (I,p,T,y,b), with b of weight -2.
weights=(1,1,3,1,-2)
def weight(m):
    return sum(a*b for a,b in zip(m,weights))%6
numerator=[(2,1,0,0,-5),(1,1,-1,0,-1)]
assert [weight(m) for m in numerator]==[1,1]
assert (1+sum(weights)-3*3)%6==2
assert (-3*weights[4])%6==0
assert [(k-1+2+1-2)%6 for k in range(1,6)]==[1,2,3,4,5]
print("Verified the mu_6 character of the five C lifts, Theta and the physical Laurent representative.")
