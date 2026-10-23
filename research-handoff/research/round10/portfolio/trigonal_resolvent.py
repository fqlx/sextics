from pathlib import Path
import sympy as s,json,itertools
HERE=Path(__file__).resolve().parent
a,b,c,w,p,r=s.symbols('a b c w p r')
r1,r2,r3=s.symbols('r1 r2 r3')
# Exact radical identity: p=r1+r2+r3, a=-sum r_i^2,
# b=sum r_i^2 r_j^2, w^3-c=product r_i^2.
aa=-(r1*r1+r2*r2+r3*r3);bb=r1*r1*r2*r2+r1*r1*r3*r3+r2*r2*r3*r3
Q=p**4+2*a*p*p+a*a-4*b
assert s.expand(Q.subs({p:r1+r2+r3,a:aa,b:bb})-8*(r1+r2+r3)*r1*r2*r3)==0
D7=s.expand(Q**2-64*p*p*(w**3-c))
# Incidence contains signed r_i in signed sum p; z=Q/(8p).
I=4*p*r*(p*p-2*p*r+2*r*r+a)-Q
assert s.expand(I.subs({p:r1+r2+r3,r:r1,a:aa,b:bb}))==0
# Verify elimination of r along the cubic incidence gives the required sextic and D7.
C=r**6+a*r**4+b*r*r+c-w**3
res=s.factor(s.resultant(C,I,r))
assert res==D7**3
# Genus3 even quotient and its Picard expression. This loses the anti character.
x,Y=s.symbols('x Y')
P4=1+4*a*x+(6*a*a-8*b)*x*x+(4*a**3-16*a*b+64*c)*x**3+(a*a-4*b)**2*x**4
assert s.expand(P4-((1+2*a*x+(a*a-4*b)*x*x)**2+64*c*x**3))==0
# For each of eight sign choices the incidence contains exactly the three
# signed r_i. Its degree-one cube characters recover the C/E anti sector.
vertices=list(itertools.product((-1,1),repeat=3))
points=[(i,sg) for i in range(3) for sg in (-1,1)]
M=s.Matrix([[int(v[i]==sg) for v in vertices] for i,sg in points])
anti=s.Matrix([[int(i==j)*(1 if sg==1 else -1) for i,sg in points] for j in range(3)])
assert anti*M*M.T==4*anti
flip=s.zeros(6)
for i,(j,sg) in enumerate(points):flip[i,points.index((j,-sg))]=1
assert M*M.T==2*(s.eye(6)-flip)+2*s.ones(6)
# The norm elliptic character is the product of the three signs. It is killed.
norm=s.Matrix([s.prod(v) for v in vertices]);assert M*norm==s.zeros(6,1)
# central sign negation fixes q=p^2 and negates all three anti characters.
central=s.zeros(8)
for i,v in enumerate(vertices): central[i,vertices.index(tuple(-t for t in v))]=1
assert (anti*M)*central==-(anti*M)
result={'radical_identity':True,'incidence_resultant_is_D7_cubed':True,'degree_one_cube_projector_square':4,'norm_elliptic_character_killed':True,'actual_anti_character_preserved_on_genus7':True,'genus3_squared_quotient_kills_actual_anti_character':True,'D7':str(D7),'incidence':str(I),'D3_picard':str(P4),'genus_D7':7,'genus_D3':3,'C_genus':4,'E_genus':1,'status':'exact algebraic correspondence and character projector; no support/uniruledness/certificate claim'}
(HERE/'trigonal_resolvent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
