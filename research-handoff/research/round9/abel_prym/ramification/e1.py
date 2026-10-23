from pathlib import Path
from fractions import Fraction
import json,time,yaml
import flint
HERE=Path(__file__).parent
start=time.monotonic();p=1000003
rec=yaml.safe_load(Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec').read_text())
F={tuple(ex):Fraction(c) for c,ex in rec['polynomialData']['F']['terms']}
A={tuple(ex):Fraction(c) for c,ex in rec['polynomialData']['A']['terms']}

def mons(n,d):
 if n==1:return [(d,)]
 return [(i,)+e for i in range(d+1)for e in mons(n-1,d-i)]
def diff(f,i):
 out={}
 for ex,c in f.items():
  if ex[i]:
   ee=list(ex);ee[i]-=1;out[tuple(ee)]=c*ex[i]
 return out
def mul(f,g):
 out={}
 for a,c in f.items():
  for b,d in g.items():
   e=tuple(x+y for x,y in zip(a,b));out[e]=out.get(e,0)+c*d
 return {e:c for e,c in out.items()if c}
def md(c):return c.numerator*pow(c.denominator,-1,p)%p
D={(0,0,3,0,0,0):Fraction(2),(3,0,0,0,0,0):Fraction(5,7),(1,0,0,0,1,1):Fraction(5,7),(0,1,0,1,1,0):Fraction(5,7)}
# Literal derivative identity establishes the support from the pinned F.
Fx=diff(F,2)
assert Fx==mul({(0,0,2,0,0,0):Fraction(3)},D)
rows=mons(6,9);lookup={e:i for i,e in enumerate(rows)};coeff=mons(6,4)
labels=[(i,e)for i in range(6)for e in coeff]
mat=[[0]*(len(labels)+1)for e in rows]
for j,(i,e)in enumerate(labels):
 for ex,c in diff(F,i).items():
  ee=tuple(a+b for a,b in zip(ex,e));mat[lookup[ee]][j]=md(c)
for ex,c in mul(A,D).items():mat[lookup[ex]][-1]=md(c)
M=flint.nmod_mat(mat,p)
rank_aug=M.rank()
rank_coeff=flint.nmod_mat([r[:-1]for r in mat],p).rank()
assert rank_coeff==len(labels)and rank_aug==len(labels)+1
out={'target':rec['id'],'prime':p,'support':'D=2*X2^3+(5/7)*(X0^3+X0*Y1*Y2+X1*Y0*Y1)','literal_derivative_identity':'F_X2=3*X2^2*D','degree':9,'number_rows':len(rows),'coefficient_columns':len(labels),'modular_coefficient_rank':rank_coeff,'modular_augmented_rank':rank_aug,'exact_char0_conclusion':'The augmented matrix has a nonzero 757-minor mod p with p not dividing rational denominators, hence rank_QQ>=757. The coefficient matrix has only756 columns, hence AD is not in the degree9 Jacobian ideal over QQ or C. No q1 certificate can be supported on this cubic or any power of its reduced support.','scope':'Only this prescribed cubic support. No statement about unions or general certificates.','seconds':round(time.monotonic()-start,3)}
(HERE/'e1.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
