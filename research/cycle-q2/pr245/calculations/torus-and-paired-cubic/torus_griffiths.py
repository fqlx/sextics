"""Finite exact algebra behind the unrestricted Laurent-torus diagnostic."""
from fractions import Fraction as Q
from itertools import permutations
from math import comb

def perm_sign(row):
    return (-1)**sum(x>y for i,x in enumerate(row) for y in row[i+1:])
chars=((-2,3,-2,1,0),(-1,0,-1,0,0),(-3,0,3,0,0),(0,0,0,0,1),(-2,2,0,0,0))
det=0
for r in permutations(range(5)):
    v=perm_sign(r)
    for i,j in enumerate(r):v*=chars[i][j]
    det+=v
assert det==12
def pull(exponents):
    return tuple(sum(exponents[i]*chars[i][j] for i in range(5)) for j in range(5))
def translate(a,b):
    assert len(a)==len(b)
    return tuple(i+j for i,j in zip(a,b))
# Character order (I,p,T,y,b); target torus order (X0,X1,Y0,Y1,Y2).
# G=p^3 F. Record G/p^3 in the original chart.
G={(0,3,0,6,0):1,(0,3,0,0,0):1,(0,2,0,1,0):Q(1,2),
   (1,1,0,1,0):Q(1,2),(6,0,3,0,-9):1,(0,0,1,0,0):1,
   (0,0,-1,0,3):1,(0,0,-1,0,0):1,(1,0,0,0,-1):Q(1,2)}
original={(6,0,0,0,0):1,(0,6,0,0,0):1,(0,0,6,0,0):1,(0,0,0,6,0):1,
          (0,0,0,0,6):1,(0,0,0,0,0):1,
          (3,1,1,1,0):Q(1,2),(0,3,0,1,1):Q(1,2),(1,0,1,0,1):Q(1,2)}
assert {pull(translate(m,(0,-3,0,0,0))):v for m,v in G.items()}==original
# N times ordinary volume, then common monomial and G^-3, divided by the
# original dlog volume coefficient to return to ordinary homogeneous residue.
ambient_n={(2,1,0,0,-5):Q(1,6),(1,1,-1,0,-1):2}
shift=(1,-8,1,1,1)
new={translate(pull(translate(m,shift)),(-1,)*5):v for m,v in ambient_n.items()}
assert new=={(5,0,3,2,0):Q(1,6),(2,5,2,1,0):2}
def homogeneous(m,degree):
    x0,x1,y0,y1,y2=m
    return(x0,x1,degree-sum(m),y0,y1,y2)
nf={homogeneous(m,12):v for m,v in new.items()}
ff={homogeneous(m,6):v for m,v in original.items()}
M=(2,0,2,2,1,0)
A=(2,2,3,2,2,1)
jac={translate(translate(m,M),(0,-1,0,0,0,0)):Q(v)*m[1]/3 for m,v in ff.items() if m[1]}
nf[A]=Q(1,2)
assert jac==nf and M[1]==0
# The actual diagonal domination holds by absolute coefficient column sums.
sizes=[]
for i in range(6):
    sizes.append(sum(abs(Q(c)*m[i]/6) for m,c in ff.items() if m[i]!=6))
assert sizes==[Q(1,3)]*3+[Q(1,6)]*3
dimension=comb(17,5)-6*comb(12,5)+15*comb(7,5)
assert dimension==1751 and max(A)<5
print('Verified degree-12 torus isogeny, G=p^3 F, and pullback of the residual numerator.')
print('Verified N_h+(1/2)A=(1/3)X0^2 X2^2 Y0^2 Y1 dF/dX1 with vanishing multiplier divergence.')
print('Largest Jacobian step has norm',max(sizes),'and the degree-12 standard monomial basis has size',dimension)
# Paired cubic over the alpha,beta,gamma base, with v=V/U and w=W/U.
# Source order (u,p,T,y,b) and target order (alpha,beta,gamma,v,w).
paired_chars=((-2,1,0,0,0),(-1,0,0,0,1),(3,0,0,0,0),(0,0,1,0,0),(0,0,0,1,0))
def paired_pull(m):
    return tuple(sum(m[i]*paired_chars[i][j] for i in range(5)) for j in range(5))
def determinant(rows):
    ans=0
    for r in permutations(range(len(rows))):
        term=perm_sign(r)
        for i,j in enumerate(r):
            term*=rows[i][j]
        ans+=term
    return ans
C={(0,0,0,0,0):1,(6,0,0,0,0):1,(0,0,0,3,0):1,(0,6,0,3,0):1,
   (0,0,0,0,3):1,(0,0,6,0,3):1,(1,1,0,1,0):Q(1,2),
   (0,1,1,2,1):Q(1,2),(1,0,1,0,2):Q(1,2)}
H={(0,3,0,0,0):1,(0,3,0,6,0):1,(1,1,0,1,2):Q(1,2),
   (0,0,-1,0,3):1,(6,0,3,0,3):1,(0,2,0,1,0):Q(1,2),
   (1,0,0,0,1):Q(1,2),(0,0,1,0,0):1,(0,0,-1,0,0):1}
assert {translate(paired_pull(m),(3,0,0,0,0)):c for m,c in H.items()}==C
assert determinant(paired_chars)==3 and paired_pull((1,)*5)==(0,1,1,1,1)
# Convert the two reduced numerators, accounting for ordinary volume
# 3/alpha and the denominator change 1/H^3=alpha^9/C^3.
old={(2,1,0,0,1):Q(1,6),(1,1,-1,0,3):2}
N={translate(paired_pull(m),(8,0,0,0,0)):3*c for m,c in old.items()}
target=(2,2,1,2,2)
N[target]=Q(3,2)
# In ordinary coordinates Q^v=2 alpha^2 beta v w and Q^beta=-alpha^2 beta^2 w.
field={3:((2,1,0,1,1),2),1:((2,2,0,0,1),-1)}
def derivative_term(m,c,i):
    e=list(m)
    e[i]-=1
    return tuple(e),c*m[i]
q_of_c={}
divergence={}
for i,(q,e) in field.items():
    d,n=derivative_term(q,e,i)
    divergence[d]=divergence.get(d,0)+n
    for m,c in C.items():
        d,n=derivative_term(m,c,i)
        k=translate(q,d)
        q_of_c[k]=q_of_c.get(k,0)+e*n
assert {m:c for m,c in q_of_c.items() if c}==N
assert not any(divergence.values())
print('Verified H=alpha^-3 C, volume factor 3/alpha, and the exact paired-cubic current Q(C)=N+(3/2)A_pair.')
