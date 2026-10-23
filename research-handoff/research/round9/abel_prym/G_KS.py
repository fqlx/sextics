"""Test the physical b-direction Prym Higgs map on the normalized G divisor."""
from pathlib import Path
from fractions import Fraction
import pickle,json,sympy as s,time
HERE=Path(__file__).parent;start=time.monotonic();p=1009
cc=5*pow(7,-1,p)%p
native=pickle.loads(Path('/workspace/research/round8/coupled_source/coordinate_fields.pickle').read_bytes())
actual=pickle.loads(Path('/workspace/research/round9/cyclic_full/actual_fast.pickle').read_bytes())
conj=pickle.loads(Path('/workspace/research/round9/cyclic_full/conjugate_fast.pickle').read_bytes())
W,h,t,L,r,x=actual['symbols']
def md(c):
 c=Fraction(str(c));return c.numerator*pow(c.denominator,-1,p)%p
def ev(poly,point,derivative=None):
 out=0
 for ex,c in poly.items():
  ee=list(ex);v=md(c)
  if derivative is not None:
   if not ee[derivative]:continue
   v=v*ee[derivative]%p;ee[derivative]-=1
  for q,n in zip(point,ee):v=v*pow(q,n,p)%p
  out+=v
 return out%p
def ep(f):
 num,den=s.fraction(s.cancel(f));return s.Poly(num,L,r,x).as_dict(),s.Poly(den,L,r,x).as_dict()
def er(f,pt):return ev(f[0],pt)*pow(ev(f[1],pt),-1,p)%p
entries={}
for name,block,rows,cols in [('actual',actual,[0,1],[2]),('conjugate',conj,[0],[1,2])]:
 entries[name]={(i,j):{z:ep(block['connection'][z][i,j])for z in ['L','r','x']}for i in rows for j in cols}
records=[]
for vv in range(1,80):
 for uu in range(1,p):
  if(uu*uu+cc*uu+1+pow(vv,6,p))%p or (uu+1)%p==0:continue
  aa=-uu*pow(vv*(uu+1),-1,p)%p
  for bb in [1,2,4,7]:
   pt=(aa,bb,vv)
   try:
    vals={k:ev(poly,pt)for k,poly in native['polynomials'].items()}
    A,B,S,H,J=[vals[k]for k in ['A','B','S','H','J']]
    LL=H*pow(3*A*A,-1,p)%p;rr=J*pow(B*A,-1,p)%p;xx=3*B**3*pow(A,-1,p)%p
    cp=(LL,rr,xx)
    db={k:ev(poly,pt,1)for k,poly in native['polynomials'].items()}
    DbL=(db['H']*pow(3*A*A,-1,p)-2*LL*db['A']*pow(A,-1,p))%p
    Dbr=(db['J']*pow(B*A,-1,p)-rr*(db['B']*pow(B,-1,p)+db['A']*pow(A,-1,p)))%p
    Dbx=(9*B*B*db['B']*pow(A,-1,p)-xx*db['A']*pow(A,-1,p))%p
    D=dict(zip(['L','r','x'],[DbL,Dbr,Dbx]))
    ks={name:{str(ij):sum(D[z]*er(ff,cp)for z,ff in by.items())%p for ij,by in all_e.items()}for name,all_e in entries.items()}
    assert((1+pow(vv,6,p))*pow(1+aa*vv,2,p)-cc*aa*vv*(1+aa*vv)+aa*aa*vv*vv)%p==0
    records.append({'v':vv,'u':uu,'a':aa,'b':bb,'canonical':cp,'d_b_parameters':D,'Higgs_hol_to_eta':ks,'nonzero':any(y for q in ks.values()for y in q.values())})
    if len(records)>=4:break
   except ZeroDivisionError:continue
  if len(records)>=4:break
 if len(records)>=4:break
assert len(records)==4 and all(q['nonzero']for q in records)
out={'prime':p,'normalization':'u²+c*u+1+v6=0,a=−u/[v(u+1)]','direction':'physical d/db at fixed a,v (G independent b)','records':records,'conclusion':'The b-line is not generically Prym-isoperiodic on the normalized G support. A good finite-prime nonzero value of these exact rational hol-to-eta coefficients proves their characteristic-zero nonidentity. This does not determine H20 or the Gysin source image.','seconds':round(time.monotonic()-start,3)}
(HERE/'G_KS.json').write_text(json.dumps(out,indent=2,default=int)+'\n');print(json.dumps(out,indent=2,default=int))
