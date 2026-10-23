import current_search as c
import numpy as np,json,sympy as s
from pathlib import Path
results=json.loads(Path(__file__).with_name('current-search-results.json').read_text())
for case in results:
 if not case['consistent_evaluations']:continue
 p=case['prime'];D=s.sympify(case['denominator']);degree=case['degree'];rng=np.random.default_rng(846475);points=rng.integers(1,p,size=(400,3))
 nums=[[0]*4 for i in range(3)]
 for item in case['candidate']:
  i,j,e,a=item['i'],c.bs.index(item['j']),item['monomial'],item['coefficient']
  nums[i][j]+=a*c.x**e[0]*c.y**e[1]*c.z**e[2]
 dd=c.evaluate(c.poly(D,p),points,p);ll=c.evaluate(c.poly(c.Li,p),points,p)
 out=np.zeros((len(points),4),dtype=np.int64)
 for i in range(3):
  di=c.evaluate(c.poly(D.diff(c.vs[i]),p),points,p)
  for j in range(4):
   nn=c.evaluate(c.poly(nums[i][j],p),points,p)
   dn=c.evaluate(c.poly(s.diff(nums[i][j],c.vs[i]),p),points,p)
   out[:,j]=(out[:,j]+ll*(dd*dn%p-nn*di%p))%p
   for k in range(4):
    bb=c.evaluate(c.poly(c.B[i][k,j],p),points,p)
    out[:,k]=(out[:,k]+dd*nn%p*bb)%p
 rhs=np.column_stack([c.evaluate(c.poly((-c.AA*D**2*c.AH[k,0]/6).subs(c.sub),p),points,p)for k in range(4)])
 residual=(out-rhs)%p
 print(case['name'], 'fresh residual nonzero entries',np.count_nonzero(residual),'/',residual.size,flush=True)
