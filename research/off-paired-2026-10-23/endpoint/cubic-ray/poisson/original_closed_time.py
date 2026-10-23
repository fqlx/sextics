"""One canonical closed-time attempt on the actual original cubic-ray cover.

Closed eta is a constant combination of df and dlog f for 15 natural f.
The original volume is dx da du dv and H,C Poisson commute exactly.
No degree escalation or assertion of rational nonexistence follows.
"""
import sys,json
from pathlib import Path
import sympy as S
import numpy as np
from closed_form_closure import encode,evaluate
root=Path(__file__).parent
sys.path.insert(0,str(root.parents[1]/'additive'))
from block_modular import solve_mod

x,a,u,v=S.symbols('x a u v');qs=[x,a,u,v]
H=1+x**6+a**6;C=1+u**6+v**6
b1=x*u/2;b2=x**3*a*u*v/2;b3=x*a*v/3;B=b1+b2+b3;D=4*B**3+27*C*H**2
hs={'x':x,'a':a,'u':u,'v':v,'H':H,'B':B,'C':C,'D':D,
    'xa':x*a,'uv':u*v,'xa+uv':x*a+u*v,'b1':b1,'b2':b2,'b3':b3,'HC':H*C}
def bracket(F,G):return S.diff(F,x)*S.diff(G,a)-S.diff(F,a)*S.diff(G,x)+S.diff(F,u)*S.diff(G,v)-S.diff(F,v)*S.diff(G,u)
Z=lambda f:3*C*H/B*bracket(B,f)-H*bracket(C,f)-2*C*bracket(H,f)

def run(p=1009):
 labels=[];expressions=[]
 for name,h in hs.items():
  dz=S.cancel(Z(h))
  for mode,expr in [('d',dz),('dlog',dz/h)]:labels.append(mode+'('+name+')');expressions.append(encode(expr,qs))
 rng=np.random.default_rng(819473)
 def sample(n):
  points=[]
  while len(points)<n:
   pt=rng.integers(1,p,size=(4,1),dtype=np.int64)
   try:[evaluate(e,pt,p)for e in expressions]
   except ZeroDivisionError:continue
   points.append(pt[:,0])
  return np.array(points).T
 values=sample(45);mat=np.column_stack([evaluate(e,values,p)for e in expressions]);rhs=np.ones(mat.shape[0],dtype=np.int64)
 rank,sol=solve_mod(mat,rhs,p)
 report={'prime':p,'closed_time_forms':labels,'rank':rank,'points':len(rhs),'consistent':sol is not None,
         'criterion':'eta(Z)=1, Z=3CH/B X_B-H X_C-2C X_H','symplectic_form':'dx wedge da+du wedge dv'}
 if sol is None:report['status']='no candidate in this finite original-cover closed-time family'
 else:
  fresh=sample(300);res=(np.column_stack([evaluate(e,fresh,p)for e in expressions])@sol-1)%p
  report['fresh_nonzero_residuals']=int(np.count_nonzero(res));report['candidate']={name:int(c)for name,c in zip(labels,sol)if c}
  report['status']='modular candidate requiring exact lifting'if not np.any(res)else'fresh points reject candidate'
 (root/'original-closed-time-results.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':run()
