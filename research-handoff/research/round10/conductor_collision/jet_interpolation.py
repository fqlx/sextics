"""Exact split-surjectivity of generic-Gamma adjoint graded jet maps.
This addresses graded generic cone defects; special-point/torsion corrections
and actual global Leray compatibility are deliberately separate.
"""
from pathlib import Path
import json,pickle,math
H=Path(__file__).parent

def mons(d,n):
 if n==1:
  yield (d,);return
 for i in range(d+1):
  for e in mons(d-i,n-1):yield(i,)+e

def add(a,b):return tuple(x+y for x,y in zip(a,b))
# Gamma: X2^6+(5/7)X0^3 X2^3+X0^6+X1^6=0, leading X2^6.
# Thus X2 exponent<6 is an exact basis, not a modular count.
levels=[]
for n in range(10):
 d=10-n;m=22+n
 xb=[e for e in mons(m,3)if e[2]<6]
 yb=[]
 # All plane forms vanishing at b=S6=0: b times degree(d-1) forms,
 # plus S6 times binary degree(d-6) forms.  Supports do not overlap.
 for e in mons(d,3):
  if e[1]>0:yb.append({e:1})
 if d>=6:
  for i in range(d-5):
   e=(i,0,d-6-i);yb.append({add(e,(6,0,0)):1,add(e,(0,0,6)):1})
 # Every tensor basis element has the literal homogeneous lift x^e*yform;
 # after restricting to Gamma its X2 degree<6 basis coefficient is unchanged.
 assert len(xb)==6*m-9
 assert len(yb)==(d+1)*(d+2)//2-min(d+1,6)
 chars={}
 for xx in xb:
  for yy in yb:
   ch=(xx[2]%3,d%2)
   chars[str(ch)]=chars.get(str(ch),0)+1
 levels.append(dict(n=n,normalJetDegree=d,coefficientDegree=m,gammaBasis=xb,nodeAdjointBasis=yb,rankR1=len(yb),gammaSections=len(xb),splitSurjectionRank=len(xb)*len(yb),characterRanks=chars))
packet=dict(gammaDegree=6,gammaGenus=10,normalBundle='O_Gamma(1)^3',exceptionalBidegree=[19,13],exceptionalConormal='O_Gamma(-1) external_tensor O_P2(1)',relativeCanonicalNormalized='O_Gamma(19) external_tensor I_sixnodes(10)',R1graded='O_Gamma(-19-n) tensor H0(I_sixnodes(10-n))^dual',dualH1='H0(O_Gamma(22+n)) tensor H0(I_sixnodes(10-n))',levels=levels,localGeometricGenus=sum(x['rankR1']for x in levels),totalSplitRank=sum(x['splitSurjectionRank']for x in levels),scope='Split graded jet maps exact over QQ and equivariant in mu3/globalY. Compatibility with the actual Leray boundary and special-point torsion not asserted.')
pickle.dump(packet,open(H/'jet_interpolation.pickle','wb'))
summary={k:v for k,v in packet.items()if k!='levels'};summary['levels']=[{k:v for k,v in u.items()if k not in ['gammaBasis','nodeAdjointBasis']}for u in levels]
(H/'jet_interpolation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
