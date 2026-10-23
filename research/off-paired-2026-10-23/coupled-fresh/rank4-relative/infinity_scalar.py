import sympy as s,json
from pathlib import Path
H,C=s.symbols('H C')
d=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
def mat(k):return s.Matrix([[s.sympify(x,locals={'H':H,'C':C}) for x in col]for col in d[k]['columns']]).T
MH,MC=mat('H'),mat('C');cols=[s.Matrix([1,0,0,0])]
for n in range(3):cols.append((cols[-1].diff(C)+MC*cols[-1]).applyfunc(s.cancel))
T=s.Matrix.hstack(*cols)
d2=json.loads(Path('/workspace/off-paired-research-new/endpoint/third-kind-connection.json').read_text())
cH=s.Matrix([s.sympify(x,locals={'H':H,'C':C})for x in d2['columns']['H']]);cC=s.Matrix([s.sympify(x,locals={'H':H,'C':C})for x in d2['columns']['C']])
assert (cH+2*C*cC/(3*H)).applyfunc(s.cancel)==s.zeros(4,1)
m=(T.inv()*cC).applyfunc(s.factor)
print('m coefficients:')
for x in m:print(x)
xi=s.Function('xi')(C)
K=sum((-1)**j*s.diff(m[j]*xi,C,j)for j in range(4))
K=s.collect(s.expand(K),[s.diff(xi,C,j)for j in range(4)])
ks=[s.factor(K.coeff(s.diff(xi,C,j)))for j in range(4)]
print('K coefficients (D^j):')
for x in ks:print(x)
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/infinity-scalar.json').write_text(json.dumps({'m':[str(x)for x in m],'K_coefficients_low_to_high':[str(x)for x in ks]},indent=2)+'\n')
