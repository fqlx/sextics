"""Exact primitive homogeneous physical effective-section support."""
from pathlib import Path
from fractions import Fraction
import pickle,json,math,functools,time
HERE=Path(__file__).parent;start=time.monotonic()
data=pickle.loads((HERE/'effective_physical.pickle').read_bytes())['t_old_over_h2']
num={e:Fraction(c)for e,c in data['num'].items()};den={e:Fraction(c)for e,c in data['den'].items()}
ab=max(i+j for i,j,k in list(num)+list(den));vd=max(k for i,j,k in list(num)+list(den))
raw={}
for poly,sgn,offset in [(den,1,0),(num,-1,1)]:
 for(i,j,k),c in poly.items():
  ex=(vd-k+2*offset,k,0,i,j,ab-i-j+2*(1-offset))
  raw[ex]=raw.get(ex,Fraction(0))+sgn*c
raw={e:c for e,c in raw.items()if c}
minimum=tuple(min(e[i]for e in raw)for i in range(6))
raw={tuple(a-b for a,b in zip(e,minimum)):c for e,c in raw.items()}
den_lcm=simple_lcm=functools.reduce(math.lcm,(c.denominator for c in raw.values()),1)
ints={e:int(c*den_lcm)for e,c in raw.items()};g=functools.reduce(math.gcd,(abs(c)for c in ints.values()))
ints={e:c//g for e,c in ints.items()}
assert len({sum(e)for e in ints})==1
degree=sum(next(iter(ints)))
(HERE/'effective_graph.pickle').write_bytes(pickle.dumps({'variables':('X0','X1','X2','Y0','Y1','Y2'),'degree':degree,'D':ints}))
(HERE/'effective_graph.json').write_text(json.dumps({'degree':degree,'terms':len(ints),'removed_coordinate_factor':minimum,'max_coefficient_digits':max(len(str(abs(c)))for c in ints.values()),'literal_definition':'Primitive homogeneous numerator of Y2² - [t_old/h²](Y0/Y2,Y1/Y2,X1/X0)*X0².','scope':'Exact support from source-specific relative Schiffer graph; not a certificate.'},indent=2)+'\n')
print((HERE/'effective_graph.json').read_text())
