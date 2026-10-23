"""Test flatness of the unique actual holomorphic Higgs-kernel line on G.
A nonzero wedge is an exact rational nonidentity; no all-source exclusion.
"""
from pathlib import Path
from fractions import Fraction
import pickle,json,sympy as s,time
HERE=Path(__file__).parent;start=time.monotonic();p=1009
native=pickle.loads(Path('/workspace/research/round8/coupled_source/coordinate_fields.pickle').read_bytes())
actual=pickle.loads(Path('/workspace/research/round9/cyclic_full/actual_fast.pickle').read_bytes())
W,h,t,L,r,x=actual['symbols'];pars=(L,r,x)
def md(c):
 c=Fraction(str(c));return c.numerator*pow(c.denominator,-1,p)%p
def ev(poly,point,degree=0,var=1):
 out=0
 for ex,c in poly.items():
  ee=list(ex);vv=md(c)
  for j in range(degree):
   if not ee[var]:vv=0;break
   vv=vv*ee[var]%p;ee[var]-=1
  for q,n in zip(point,ee):vv=vv*pow(q,n,p)%p
  out+=vv
 return out%p

def ep(f):
 num,den=s.fraction(s.cancel(f));return s.Poly(num,*pars).as_dict(),s.Poly(den,*pars).as_dict()
def er(f,pt):return ev(f[0],pt)*pow(ev(f[1],pt),-1,p)%p
entries={z:[[ep(actual['connection'][z][i,j])for j in range(3)]for i in range(3)]for z in ['L','r','x']}
def ed(f,pt,k):
 n,d=ev(f[0],pt),ev(f[1],pt)
 return (ev(f[0],pt,1,k)*d-n*ev(f[1],pt,1,k))*pow(d*d,-1,p)%p


def add(a,b):return[(a[i]+b[i])%p for i in range(3)]
def scale(a,q):return[x*q%p for x in a]
def mul(a,b):return[sum(a[j]*b[i-j]for j in range(i+1))%p for i in range(3)]
def inv(a):
 out=[pow(a[0],-1,p)]
 for i in range(1,3):out.append(-sum(a[j]*out[i-j]for j in range(1,i+1))*out[0]%p)
 return out
records=[]
for bb in [1,2,4,7]:
 pt=(580,bb,2)
 vals={name:[ev(poly,pt,j)*pow(2,-1,p)%p if j==2 else ev(poly,pt,j)for j in range(3)]for name,poly in native['polynomials'].items()}
 A,B,S,H,J=[vals[k]for k in ['A','B','S','H','J']]
 pjets=[scale(mul(H,mul(inv(A),inv(A))),pow(3,-1,p)),mul(J,mul(inv(B),inv(A))),scale(mul(mul(mul(B,B),B),inv(A)),3)]
 cp=[z[0]for z in pjets];d=[z[1]for z in pjets];dd=[2*z[2]%p for z in pjets]
 Nb=[[sum(d[z]*er(entries[name][i][j],cp)for z,name in enumerate(['L','r','x']))%p for j in range(3)]for i in range(3)]
 dNb=[[sum(dd[z]*er(entries[name][i][j],cp)+d[z]*sum(d[k]*ed(entries[name][i][j],cp,k)for k in range(3))for z,name in enumerate(['L','r','x']))%p for j in range(3)]for i in range(3)]
 k0,k1=Nb[0][2],Nb[1][2];dk0,dk1=dNb[0][2],dNb[1][2]
 line=[k1,-k0%p,0]
 nabla=[(dk1+Nb[0][0]*k1-Nb[1][0]*k0)%p,(-dk0+Nb[0][1]*k1-Nb[1][1]*k0)%p,0]
 assert(Nb[0][2]*line[0]+Nb[1][2]*line[1])%p==0
 wedge=(line[0]*nabla[1]-line[1]*nabla[0])%p
 assert wedge
 records.append({'a_b_v':pt,'parameters':cp,'d_b_parameters':d,'d_bb_parameters':dd,'N_b':Nb,'d_b_N_b':dNb,'hol_Higgs_kernel_line':line,'hol_covariant_derivative':nabla,'kernel_flatness_wedge':wedge})
out={'prime':p,'records':records,'conclusion':'The unique actual holomorphic kernel of the b-Higgs map is not invariant under the b-Gauss-Manin connection. Together with the nonzero conjugate hol-to-eta map, this excludes a flat holomorphic line in either eigencharacter along generic b on G, hence excludes a constant CM E0 summand of the restricted Prym family. It does not determine all H20, or exclude other source/correspondence routes.','convention':'nabla(coefficient column)=d+N^T; h=(N_b[1,2],-N_b[0,2],0)','seconds':round(time.monotonic()-start,3)}
(HERE/'G_fixed_part.json').write_text(json.dumps(out,indent=2,default=int)+'\n');print(json.dumps(out,indent=2,default=int))
