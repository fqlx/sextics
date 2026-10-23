"""Source-preserving infinity gauge killing normal C and C² coefficients."""
import runpy,sympy as s,json
from pathlib import Path
v=runpy.run_path(str(Path(__file__).with_name('verify_source_gauged_ore.py')))
C,H,D=v['C'],v['H'],v['D'];mul,adj,add=v['mul'],v['adj'],v['add'];r=v['r'];U,V,R,S,L,M=[v[k]for k in ('U','V','R','S','L','M')]
E=[-3*r,2*C*r]
B12=add(adj(V),mul(adj(S),E))
A12=add(adj(U),mul(adj(R),E),-1)
checks=[]
checks.append(not add(add(mul(adj(L),A12),mul(adj(M),B12)),[s.Integer(1)],-1))
for n in (1,2):checks.append(s.cancel(sum(x*s.diff(C**n,C,j)for j,x in enumerate(B12)))==0)
# (theta−1)(theta−2)=C² D²−2 C D+2.
Bt,rem=v['rightdiv'](B12,[2,-2*C,C*C]);checks.append(not rem)
assert all(checks),checks
out={'checks':len(checks),'passed':True,'meaning':'L* A12+M* B12=1,B12=Bt(theta−1)(theta−2); no horizontal closure','E':[str(s.factor(x))for x in E],'B12':[str(s.factor(x))for x in B12],'Bt':[str(s.factor(x))for x in Bt],'A12':[str(s.factor(x))for x in A12]}
Path(__file__).with_name('two-normal-gauge.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
