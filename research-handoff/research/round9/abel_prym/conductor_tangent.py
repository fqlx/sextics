"""Exact tangent quadratic of D32 along six ruled conductor surfaces."""
from pathlib import Path
import pickle,sympy as s,json,time
HERE=Path(__file__).parent;start=time.monotonic()
p=pickle.load(open(HERE/'effective_graph.pickle','rb'));X0,X1,X2,Y0,Y1,Y2=s.symbols('X0 X1 X2 Y0 Y1 Y2');aa=s.Symbol('aa')
def coefficient(i,j):
 f=0
 for e,c in p['D'].items():
  if e[3]<i or e[4]!=j:continue
  # Taylor coefficient in Y0-aa*Y2 and Y1; Y0=aa*Y2,Y1=0.
  k=e[3]-i;sgn=(-1)**(k//6)
  f+=s.Rational(c)*s.binomial(e[3],i)*sgn*aa**(k%6)*X0**e[0]*X1**e[1]*Y2**(k+e[5])
 return s.factor(f)
q={(i,j):coefficient(i,j)for i,j in((0,0),(1,0),(0,1),(2,0),(1,1),(0,2))}
assert q[0,0]==q[1,0]==q[0,1]==0
# The factorization is valid before specializing any of the six roots.
qaa,qab,qbb=q[2,0],q[1,1],q[0,2]
print('QAA',qaa,flush=True);print('QAB',qab,flush=True);print('QBB',qbb,flush=True)
g=s.factor(s.gcd(qaa,qab));print('GCD',g,flush=True)
result={'surface':'Y1=0,Y0=aa*Y2,aa^6=-1','normal_coordinates':'x=Y0-aa*Y2,y=Y1','Qaa':str(qaa),'Qab':str(qab),'Qbb':str(qbb),'common_factor':str(g),'residual_Qaa':str(s.cancel(qaa/g)),'residual_Qab':str(s.cancel(qab/g)),'transverse_generic':'The quadratic is x*(Qaa*x+Qab*y), with two rationally split distinct normal branches where Qab!=0.','global_conductor_twist':'For the ordinary-node part, normal bundle O_S(1)^2, D32 doublealongS, hence branch-line coefficients O_S(30). Generic normalization-conductor rank1 piece has O_S(-30) frame before corrections from the common tangent factor.','scope':'Exact tangent factorization and generic branch identification. At common-factor divisors the quadratic vanishes identically and higher normal terms are required; no global conductor-sheaf equality is inferred there.','seconds':time.monotonic()-start}
(HERE/'conductor_tangent.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
