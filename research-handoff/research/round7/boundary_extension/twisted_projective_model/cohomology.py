"""Exact toric-bundle/Koszul cohomology enumeration for the RAW CI."""
from itertools import combinations
from pathlib import Path
import json,math

E=[(12,12,4,6),(12,12,5,6),(12,12,6,6)]
def base_cohom(d):
 if -1 in d:return None
 return sum(x <= -2 for x in d), math.prod(abs(x+1) for x in d)
rows=[]
for n in (1,2,3):
 for inds in combinations(range(3),n):
  A=tuple(sum(E[i][j]for i in inds)for j in range(4))
  blocks=[];dims={}
  for j in range((A[3]-4)//2+1):
   for i in range(A[3]-4-2*j+1):
    k=A[3]-4-2*j-i
    d=(-A[0]+6+2*i+4*j,-A[1]+6+2*i+4*j,-A[2]+2+2*j)
    bc=base_cohom(d)
    if bc is None:continue
    co,dim=bc;wi=co+2;dims[wi]=dims.get(wi,0)+dim
    if wi==4:blocks.append({'fiber_monomial_exponents_U_t_z':[i,j,k],'base_degrees':d,'dimension':dim})
  rows.append({'equations':[i+1 for i in inds],'ambient_cohomology_dimensions':dims,'H4_blocks':blocks})
triple=rows[-1];p12=next(r for r in rows if r['equations']==[1,2])
assert triple['H4_blocks']==[{'fiber_monomial_exponents_U_t_z':[0,7,0],'base_degrees':(-2,-2,1),'dimension':2}]
assert p12['H4_blocks']==[{'fiber_monomial_exponents_U_t_z':[0,4,0],'base_degrees':(-2,-2,1),'dimension':2}]
out={'formula':'R2 pi_* O(-A;-d) = direct_sum O(-A+(6,6,2)+i(2,2,0)+j(4,4,2)), i+2j+k=d-4',
 'koszul_terms':rows,'H1_O_raw_CI':0,
 'reason':'Only possible total-degree1 term is H4(O(-E123)), dimension2. Its d1 map to H4(O(-E12)), dimension2, is identity because E3 contains monic t3. No higher differential can enter the total-degree1 term. This is raw CI cohomology, not resolved main-component irregularity.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
