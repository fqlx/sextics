"""Extract exact Hodge-leading boundary1forms and source binding."""
from pathlib import Path
import pickle,sympy as s,json,time
HERE=Path(__file__).parent;start=time.monotonic()
d=pickle.loads((HERE/'boundary_native.pickle').read_bytes())
L,r,x,z=s.symbols('L r x s');pars=(L,r,x,z)
def rf(v):
 def poly(p):return sum(s.Rational(c)*s.prod(a**e for a,e in zip(pars,ex))for ex,c in p.items())
 return s.cancel(poly(v['numerator'])/poly(v['denominator']))
E={name:[rf(row[2])for row in rows]for name,rows in d['connection_boundary'].items()}
print('HODGE BOUNDARY ROWS',flush=True)
for name,row in E.items():
 print(name,[str(s.factor(v))for v in row],flush=True)
# Primitive derivative's eta coefficient should have a uniform denominator.
eta0={name:row[0]for name,row in E.items()};eta1={name:row[1]for name,row in E.items()}
ratios={name:s.factor(a/b)if b else None for name,(a,b)in E.items()}
packet={'symbols':pars,'E_eta':E,'ratios':ratios}
(HERE/'hodge_leading.pickle').write_bytes(pickle.dumps(packet))
(HERE/'hodge_leading.json').write_text(json.dumps({'E_eta':{name:list(map(str,row))for name,row in E.items()},'ratios':{name:str(v)for name,v in ratios.items()},'seconds':time.monotonic()-start},indent=2)+'\n')
