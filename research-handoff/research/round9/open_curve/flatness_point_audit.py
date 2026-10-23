"""Independent finite-prime jet audit of the assembled full rank5 connection."""
from pathlib import Path
import pickle,json,random,time,sympy as s
HERE=Path(__file__).parent;start=time.monotonic();prime=1000003
boundary=pickle.loads((HERE/'boundary_native.pickle').read_bytes())
proper=pickle.loads(Path('/workspace/research/round9/cyclic_full/global_eta_complete.pickle').read_bytes())
L,r,x,ss=s.symbols('L r x s');pars=(L,r,x,ss);names=['L','r','x','s']
def parsepol(poly):
 if isinstance(poly,str):return s.Poly(s.sympify(poly.replace('^','**')),*pars).as_dict()
 return{e:s.Rational(c)for e,c in poly.items()}
def compile(rf):return tuple(parsepol(rf[k])for k in ['numerator','denominator'])
def mc(c):
 c=s.Rational(c);return int(c.p)*pow(int(c.q),-1,prime)%prime
def pe(poly,pt,deriv=None):
 ans=0
 for ex,coef in poly.items():
  ex=list(ex);a=mc(coef)
  if deriv is not None:
   if not ex[deriv]:continue
   a=a*ex[deriv]%prime;ex[deriv]-=1
  for v,k in zip(pt,ex):a=a*pow(v,k,prime)%prime
  ans+=a
 return ans%prime
def valjet(rf,pt):
 n,d=[pe(f,pt)for f in rf];di=pow(d,-1,prime)
 return n*di%prime,[(pe(rf[0],pt,i)*d-n*pe(rf[1],pt,i))*di*di%prime for i in range(4)]
zero=({}, {(0,0,0,0):s.Integer(1)})
N={}
for name in names:
 M=[[zero for j in range(5)]for i in range(5)]
 if name!='s':
  for i in range(3):
   for j in range(3):M[i][j]=compile(proper['connection'][name][i][j])
 for i in range(2):
  for j in range(5):M[i+3][j]=compile(boundary['connection_boundary'][name][i][j])
 N[name]=M
rng=random.Random(90071);records=[]
while len(records)<12:
 pt=[rng.randrange(1,200)for i in range(4)]
 try:
  evaluated={name:[[valjet(f,pt)for f in row]for row in mat]for name,mat in N.items()}
 except ValueError:continue
 for i in range(4):
  for j in range(i+1,4):
   I,J=evaluated[names[i]],evaluated[names[j]]
   for a in range(5):
    for b in range(5):
     cur=J[a][b][1][i]-I[a][b][1][j]+sum(J[a][k][0]*I[k][b][0]-I[a][k][0]*J[k][b][0]for k in range(5))
     assert cur%prime==0,(pt,names[i],names[j],a,b,cur%prime)
 records.append(pt)
out={'prime':prime,'points':records,'all6_parameter_pairs_all25_entries_zero':True,'checks':len(records)*6*25,'convention':'d_i N_j-d_j N_i+N_j*N_i-N_i*N_j=0 for derivative-of-basis row matrices','scope':'Independent finite-prime flatness jet audit; exact polynomial reduction identities are separately verified in boundary_native. This finite audit alone is not an exact rational flatness proof.','seconds':time.monotonic()-start}
(HERE/'flatness_point_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
