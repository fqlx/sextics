import json,sympy as s
from pathlib import Path
H,C=s.symbols('H C')
b=s.symbols('b')
d=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
# JSON columns -> actual matrix, then universal H=1 slice.
def matrix(k):
 return s.Matrix([[s.sympify(x,locals={'H':H,'C':C}) for x in col] for col in d[k]['columns']]).T
M=matrix('C').subs({H:1,C:b})
e=s.Matrix([1,0,0,0]); cols=[e]
for i in range(4):
 cols.append((cols[-1].diff(b)+M*cols[-1]).applyfunc(s.cancel))
T=s.Matrix.hstack(*cols[:4]); det=s.factor(T.det()); print('det',det,flush=True)
coef=(T.inv()*cols[4]).applyfunc(s.factor)
print('PF coefficients y4=sum ci yi:')
for c in coef: print(c)
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/cyclic_pf.json').write_text(json.dumps({'coordinate':'H=1,C=b','cyclic_determinant':str(det),'coefficients':[str(c) for c in coef]},indent=2)+'\n')
