import sympy as s,json
from pathlib import Path
H,C=s.symbols('H C');Delta=4*C**6-729*H**4
clean=s.cancel
def trim(A):
 while A and A[-1]==0:A.pop()
 return A
def add(A,B):return trim([clean((A[i]if i<len(A)else 0)+(B[i]if i<len(B)else 0))for i in range(max(len(A),len(B)))])
def mul(A,B):
 R=[s.Integer(0)]*(len(A)+len(B)-1)
 for i,a in enumerate(A):
  for j,b in enumerate(B):
   for k in range(i+1):R[i-k+j]+=s.binomial(i,k)*a*s.diff(b,C,k)
 return trim([clean(x)for x in R])
cs=[-55*C*C/Delta,-309*C**3/Delta,-(271*C**6-1458*H**4)/(C*C*Delta),-2*(32*C**6+729*H**4)/(C*Delta)]
L=[-cs[0],-cs[1],-cs[2],-cs[3],s.Integer(1)]
M=[2*C**3/(567*H**2),46*C**4/(2835*H**2),(20*C**6+2187*H**4)/(1890*C*H**2),Delta/(2835*H**2)]
U=[-(54328*C**12-3197394*C**6*H**4+98316585*H**8)/(1786050*C**2*H**4),
 -Delta*(4652*C**6+158193*H**4)/(3572100*C*H**4),-23*Delta**2/(1786050*H**4)]
V=[613*C**3/(63*H**2),1217*C**4/(126*H**2),(484*C**6+12393*H**4)/(210*C*H**2),23*Delta/(630*H**2)]
assert add(mul(U,L),mul(V,M))==[1]
# V is homogeneous of weight zero in 3H*dH+2C*dC, including derivative weights.
for j,v in enumerate(V):assert clean(3*H*s.diff(v,H)+2*C*s.diff(v,C)-2*j*v)==0
out={'meaning':'U L+V M=1 exactly; taking formal adjoints yields L* U*+M* V*=1',
'convention':'coefficients low to high powers of actual commuting D_C; H constant under D_C',
'U':[str(s.factor(x))for x in U], 'V':[str(s.factor(x))for x in V], 'M':[str(s.factor(x))for x in M]}
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/infinity-ore-general.json').write_text(json.dumps(out,indent=2)+'\n')
print('General-H infinity Ore identity and homogeneous V verified exactly.')
# Explicit compact forcing K=M*.
f=s.Function('f')(C)
B=s.expand(sum((-1)**j*s.diff(V[j]*f,C,j)for j in range(4)))
Bco=[s.factor(B.coeff(s.diff(f,C,j)))for j in range(4)]
print('V* coefficients:')
for x in Bco:print(x)
# Exact Euler factorization of B=V*, preserving the real physical D_C action.
def theta(v):return C*s.diff(v,C)
def op_poly(v,coeff):
 out=0;w=v
 for c in coeff:out+=c*w;w=theta(w)
 return s.expand(out)
fac=-C**3/(630*H**2)*op_poly(f,[210,-175,-72,92])+729*H**2/(630*C**3)*op_poly(f,[102,-107,-18,23])
# (2t+3)(46t^2-105t+70)=92t^3-72t^2-175t+210.
# (t-2)(t-1)(23t+51)=23t^3-18t^2-107t+102.
assert s.cancel(B-fac)==0
z=s.symbols('z');k=s.Rational(81,2)*C**2*z
Btheta_k=sum((-1)**j*s.diff(V[j]*(C*s.diff(k,C)),C,j)for j in range(4))
assert s.cancel(Btheta_k+s.Rational(308,315)*(C**3/H**2)*k)==0
print('Euler B factorization and the source-normal logarithmic coefficient passed.')
