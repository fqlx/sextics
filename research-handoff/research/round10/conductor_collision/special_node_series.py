from pathlib import Path
import pickle,sympy as s,json
H=Path(__file__).parent;d=pickle.load(open(H/'strict_normalization.pickle','rb'));a,b,t,v,e=d['variables'];parts=d['parts']
def reduce(f,k):
 out=0
 for mon,c in s.Poly(f.subs(t,1),a,b,v).terms():
  i,j,l=mon;out+=c*(-1 if i//6%2 else 1)*k**(l//6)*a**(i%6)*b**j*v**(l%6)
 return s.Poly(out,b)
res={}
for name,k in [('P0',s.Rational(-1)),('T0',s.Rational(-171,196))]:
 dd={}
 for n in [13,15]:
  ss=reduce(parts[n][2],k)
  dd[str(n)]={str(m[0]):str(s.factor(c)) for m,c in ss.terms()}
 res[name]=dd
(H/'special_node_series.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
