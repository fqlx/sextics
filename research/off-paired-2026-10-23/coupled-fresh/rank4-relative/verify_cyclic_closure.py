"""Full compact rank-four operator closure, with no source component dropped."""
import json,sympy as s
from pathlib import Path
H,C=s.symbols('H C'); d=json.loads(Path('/workspace/off-paired-research-new/endpoint/reconstructed-connection.json').read_text())
def matrix(k):
 return s.Matrix([[s.sympify(x,locals={'H':H,'C':C}) for x in col] for col in d[k]['columns']]).T
MH,MC=matrix('H'),matrix('C'); e=s.Matrix([1,0,0,0]);cols=[e]
clean=lambda v:v.applyfunc(s.cancel)
for j in range(4):cols.append(clean(cols[-1].diff(C)+MC*cols[-1]))
Delta=4*C**6-729*H**4
cs=[-55*C**2/Delta,-309*C**3/Delta,-(271*C**6-1458*H**4)/(C**2*Delta),-2*(32*C**6+729*H**4)/(C*Delta)]
assert clean(cols[4]-sum((cs[j]*cols[j] for j in range(4)),s.zeros(4,1)))==s.zeros(4,1)
for j in range(4):
 assert clean(cols[j].diff(H)+MH*cols[j]+((2+2*j)*cols[j]+2*C*cols[j+1])/(3*H))==s.zeros(4,1)
assert clean(3*H*MH+2*C*MC-s.diag(-2,-1,1,2))==s.zeros(4,4)
# The companion-current formula holds formally for any commuting coefficient derivation.
f0,f1,f2,f3,f4=s.symbols('f0:5')
def deriv(v):
 return s.diff(v,C)+sum(s.diff(v,a)*b for a,b in zip([f0,f1,f2,f3],[f1,f2,f3,f4]))
v3=f0;v2=-f1-cs[3]*f0;v1=deriv(f1+cs[3]*f0)-cs[2]*f0
v0=-deriv(v1)-cs[1]*f0
v=s.Matrix([v0,v1,v2,v3])
N=s.zeros(4)
for j in range(3):N[j+1,j]=1
for j in range(4):N[j,3]=cs[j]
res=clean(v.applyfunc(deriv)+N*v)
assert res[1:4]==[0,0,0]
expected=-f4-deriv(deriv(deriv(cs[3]*f0)))+deriv(deriv(cs[2]*f0))-deriv(cs[1]*f0)+cs[0]*f0
assert s.cancel(res[0]-expected)==0
print('Full rank-four cyclic closure, four H columns, weighted Euler identity, and adjoint-current identity passed.')
T=s.Matrix.hstack(*cols[:4])
assert s.cancel(T.det(method='domain-ge')+16533720*C**2*H**4/Delta**3)==0
print('General-H cyclic determinant passed.')
