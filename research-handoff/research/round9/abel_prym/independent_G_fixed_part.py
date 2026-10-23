"""Independent symbolic-derivative audit of the fixed-part Higgs criterion.

No native Taylor-series jet or derivative evaluator is imported.  All first
and second physical derivatives are differentiated with SymPy before modular
evaluation; connection derivatives are obtained directly from their entries.
"""
from pathlib import Path
import sympy as s,pickle,json,time
from functools import lru_cache
HERE=Path(__file__).parent;start=time.monotonic()
ref=json.loads((HERE/'G_fixed_part.json').read_text());p=ref['prime']
a,b,v=s.symbols('a b v');c=s.Rational(5,7)
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
pars=[(27*P*S**2-9*Q*R*S+2*R**3)/(3*A**2),(3*S*Q-R**2)/(B*A),3*B**3/A]
dpars=[s.diff(f,b) for f in pars];ddpars=[s.diff(f,b,2) for f in pars]
G=P*(1+a*v)**2-c*a*v*(1+a*v)+a*a*v*v
blocks={n:pickle.load(open(HERE.parent/'cyclic_full'/f'{n}_fast.pickle','rb')) for n in ('actual','conjugate')}
def evaluator(point):
 @lru_cache(None)
 def ev(e):
  if e.is_Rational:return int(e.p)*pow(int(e.q),-1,p)%p
  if e.is_Symbol:return point[e]
  if e.is_Add:return sum(ev(x) for x in e.args)%p
  if e.is_Mul:
   z=1
   for x in e.args:z=z*ev(x)%p
   return z
  if e.is_Pow:return pow(ev(e.base),int(e.exp),p)
  raise TypeError(e)
 return ev
records=[]
for record in ref['records']:
 pt=record['a_b_v'];ev=evaluator(dict(zip((a,b,v),pt)))
 cp=[ev(f) for f in pars];d=[ev(f) for f in dpars];dd=[ev(f) for f in ddpars]
 assert cp==record['parameters'] and d==record['d_b_parameters'] and dd==record['d_bb_parameters']
 out={}
 for name,data in blocks.items():
  variables=data['symbols'][3:];ce=evaluator(dict(zip(variables,cp)))
  matrices=[data['connection'][k] for k in ('L','r','x')]
  Nb=[[sum(d[j]*ce(matrices[j][i,k]) for j in range(3))%p for k in range(3)] for i in range(3)]
  dNb=[[sum(dd[j]*ce(matrices[j][i,k])+d[j]*sum(d[l]*ce(s.diff(matrices[j][i,k],variables[l])) for l in range(3)) for j in range(3))%p for k in range(3)] for i in range(3)]
  out[name]={'Nb':Nb,'dNb':dNb}
 actual=out['actual'];N=actual['Nb'];dN=actual['dNb'];line=[N[1][2],-N[0][2]%p,0]
 cov=[(dN[1][2]+sum(N[j][0]*line[j] for j in range(3)))%p,(-dN[0][2]+sum(N[j][1]*line[j] for j in range(3)))%p,sum(N[j][2]*line[j] for j in range(3))%p]
 wedge=(line[0]*cov[1]-line[1]*cov[0])%p
 assert N==record['N_b'] and dN==record['d_b_N_b']
 assert line==record['hol_Higgs_kernel_line'] and cov==record['hol_covariant_derivative'] and wedge==record['kernel_flatness_wedge'] and wedge
 assert any(out['conjugate']['Nb'][0][j] for j in (1,2))
 assert ev(G)==0 and ev(s.diff(G,a))
 uu=(-pt[0]*pt[2]*pow(1+pt[0]*pt[2],-1,p))%p
 assert (uu*uu+(5*pow(7,-1,p))*uu+1+pow(pt[2],6,p))%p==0
 assert (2*uu+5*pow(7,-1,p))%p
 # On h=1 the canonical curve must be smooth. The h=0 WP chart is
 # W^6+T^3/x=0; its gradient has no projective common zero for x !=0.
 W,H,T,L,rr,x=blocks['actual']['symbols'];cc=5*pow(7,-1,p)%p
 C=W**6+cc*(1+T)*W**3+cp[0]+cp[1]*T+pow(cp[2],-1,p)*T**3
 gb=s.groebner([C,s.diff(C,W),s.diff(C,T)],W,T,modulus=p)
 assert len(gb.polys)==1 and gb.polys[0].is_one and cp[2]
 records.append({'point':pt,'parameters':cp,'db':d,'dbb':dd,'wedge':wedge,'conjugate_higgs_row':out['conjugate']['Nb'][0][1:],'G_a':ev(s.diff(G,a)),'normalization_u':uu,'normalization_etale':True,'canonical_curve_smooth':True})
result={'prime':p,'records':records,'all_reference_entries_reproduced':True,'convention':'Connection matrices have derivative-of-basis rows, so coefficient columns use d+N^T. The line h=(N12,-N02,0) is the unique actual holomorphic Higgs kernel. Its invariant-line test is h wedge (db h+N^T h).','independent_method':'Native rational first/second derivatives and canonical matrix derivatives differentiated directly by SymPy, then recursively evaluated; no native Taylor-series jet routines imported.','specialization':'G_a and normalization 2u+c are units, all evaluated connection denominators are units, and canonical fibers are smooth. Nonzero wedges therefore prove characteristic-zero rational nonidentity on this normalization component.','scope':'Excludes a flat holomorphic line in each mu3 character along generic b, and consequently a constant CM E0 summand of this restricted Prym VHS. Does not exclude H20 of the total support, variable factors, correspondences, or other source routes.','seconds':time.monotonic()-start}
(HERE/'independent_G_fixed_part.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
