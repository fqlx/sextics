"""Exact source-current reconstruction checkpoint at j=w=1.

This is internal restricted feedback, not an exclusion theorem. Generic
local-pole bounds and all regular-singular extension hypotheses have not
been independently verified here. The positive result of this direction
is the exact generic Ui current in i-source-compact-primitive-results.json;
its full density/branch corrections remain and are pursued on the full base.
"""
import json,hashlib
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq_poly,fmpq
B=Path('/workspace/off-paired-research-new/coupled-fresh');C=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=C.gens()
ij=json.loads((B/'ruling-source/full-base-connection/rank8-ij-connections-results.json').read_text());vv=json.loads((B/'theta-compact/rank8-descended-connection-results.json').read_text())
X=fmpq_poly([0,1]);T=2;N=9*X**2-32;M=8192*N+729*X**6
vn=256*N;vd=9*X**2*M;g=vn.gcd(vd);vn=vn//g;vd=vd//g
print('v',vn,vd,flush=True)
pn=[fmpq_poly([1])];pd=[fmpq_poly([1])]
for k in range(1,7):pn.append(pn[-1]*vn);pd.append(pd[-1]*vd)
def compose(txt,k=5):
 p=fmpq_mpoly(txt,C);o=fmpq_poly([])
 for (a,b,c),co in p.to_dict().items():o+=co*X**a*pn[c]*pd[k-c]
 return o
Den=compose(ij['common_denominator'],4)
gi=[[compose(z)for z in row]for row in ij['Gamma_numerators']['i']];gv=[[compose(z)for z in row]for row in vv['GammaV_numerator']]
hn=vn.derivative()*vd-vn*vd.derivative();D=6*vn*vd*vd*Den
G=[[6*vn*vd*gi[r][c]+hn*gv[r][c] for c in range(8)]for r in range(8)]
co=D
for row in G:
 for z in row:co=co.gcd(z)
D=D//co;G=[[z//co for z in row]for row in G]
print('commonDdeg',D.degree(),'D0order',next(k for k in range(D.degree()+1) if D[k]),flush=True)
def order(p):return next((k for k in range(p.degree()+1) if p[k]),10**6)
dord=order(D);V=[[order(z)-dord+1 for z in row]for row in G]
print('iGamma valuations',V,flush=True)
s=[0]*8
for n in range(9):
 ch=False
 for r in range(8):
  for c in range(8):
   if G[r][c] and s[r]>s[c]+V[r][c]:s[r]=s[c]+V[r][c];ch=True
 if not ch:break
print('shifts',s,'negativecycle',ch,'turn',n,flush=True)
if not ch:
 from flint import fmpq_mat
 R=fmpq_mat(8,8,[G[r][c][dord-1+s[r]-s[c]]/D[dord]+(s[c] if r==c else 0) if dord-1+s[r]-s[c]>=0 else (s[c] if r==c else 0)for r in range(8)for c in range(8)])
 print('R',R,flush=True);print('char',R.charpoly().factor(),flush=True)
es=json.loads((B/'ruling-source/full-base-connection/source-euler-current-results.json').read_text()); SD=compose(es['remaining_common_denominator'],4)*vd*N
SN=[18*X**3*compose(z) for z in es['remaining_vector_numerators']]
co=SD
for z in SN:co=co.gcd(z)
SD=SD//co;SN=[z//co for z in SN]
print('sourceDen',SD.degree(),'sourceorders',[order(z)-order(SD) for z in SN],flush=True)
print('sourceshearedorders',[order(z)-order(SD)-s[r] for r,z in enumerate(SN)],flush=True)
# Candidate space is the complete local-pole space at this exact generic point,
# not an arbitrary degree expansion. Negative result will not be promoted.
low=s;high=[1,2,4,5,1,2,4,5]
L=D*SD//D.gcd(SD); GS=[[z*(L//D) for z in row]for row in G];SS=[z*(L//SD)for z in SN]
cols=[];labels=[]
for c in range(8):
 for k in range(low[c],high[c]+1):
  row=[]
  for r in range(8):
   z=GS[r][c]*X**(k+3)
   if r==c and k:z+=k*L*X**(k+2)
   row.append(z)
  cols.append(row);labels.append((c,k))
rhs=[z*X**3 for z in SS];maxdeg=max([z.degree()for col in cols for z in col]+[z.degree()for z in rhs]);nr=8*(maxdeg+1);nc=len(cols)
print('exact system',nr,nc,flush=True)
A=fmpq_mat(nr,nc+1)
for r in range(8):
 for k in range(maxdeg+1):
  z=r*(maxdeg+1)+k
  for c in range(nc):A[z,c]=cols[c][r][k]
  A[z,nc]=rhs[r][k]
RR,rank=A.rref();inconsistent=any(all(not RR[r,c]for c in range(nc))and RR[r,nc]for r in range(nr))
print('rref rank',rank,'inconsistent',inconsistent,flush=True)
if not inconsistent:
 sol=[fmpq(0)]*nc
 for r in range(rank):
  p=next(c for c in range(nc)if RR[r,c]);sol[p]=RR[r,nc]
 print('solution',list(zip(labels,map(str,sol))),flush=True)
out={
 'status':'Exact specialized reconstruction feedback only; not a certificate or a global exclusion',
 'specialization':{'j':'1','w':'1'},
 'actual_source':'9*i^3*w*(1+w^3)/(j^2*N) * (4*e_b-GammaD*e_b)',
 'equation':'P_i prime + [Gamma_i+v_i*GammaV/(6v)] P_i=actual_source',
 'i0_diagonal_shear':s,
 'candidate_laurent_lower':low,'candidate_laurent_upper':high,
 'reconstruction_rows':nr,'unknowns':nc,'augmented_rank':rank,
 'consistent_in_displayed_layout':not inconsistent,
 'scope':'These exact local calculations guide construction. They are not independently audited generic completeness bounds and are not promoted to a new relative exclusion.',
 'next':'Use the exact generic Ui/Uj full-base source currents with all density and inverse-branch corrections.',
 'source_hash':hashlib.sha256((B/'ruling-source/full-base-connection/source-euler-current-results.json').read_bytes()).hexdigest(),
 'certificate':False}
Path(__file__).with_name('i-direction-point-feedback.json').write_text(json.dumps(out,indent=2)+'\n')
