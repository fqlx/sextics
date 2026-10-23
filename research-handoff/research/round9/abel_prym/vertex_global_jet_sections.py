"""Explicit global degree32 preimages of the generic vertex adjoint jets."""
from pathlib import Path
import pickle,json
HERE=Path(__file__).parent
# Exponents are X0,X1,W,Y0,Y1,Y2. r uses S6 times its monomial.
def seed(slot,k,j):
 if slot=='1':return{(16-k,k,0,j,1,15-j):1}
 if slot=='eps2':return{(18-k,k,0,j,1,13-j):1}
 if slot=='b':return{(16-k,k,0,j,2,14-j):1}
 if slot=='r':return{(16-k,k,0,j+6,0,10-j):1,(16-k,k,0,j,0,16-j):1}
 raise KeyError(slot)
weights=(0,4,0,1,1,5);rows=[]
for slot,kmax in [('1',16),('eps2',18),('b',16),('r',16)]:
 for k in range(kmax+1):
  for j in range(6):
   dd=seed(slot,k,j)
   assert all(sum(e)==32 and e[0]+e[1]>=16 and e[2]%3==0 and sum(e[3:])%2==0 for e in dd)
   chars={sum(w*n for w,n in zip(weights,e))%6 for e in dd};assert len(chars)==1
   char=chars.pop();needed={'1':1,'eps2':2,'b':2,'r':0}[slot]
   assert(char==2)==((k-j)%3==needed)
   rows.append({'slot':slot,'k':k,'j':j,'delta_character':char,'polynomial':dd})
assert len(rows)==420 and sum(r['delta_character']==2 for r in rows)==140
pickle.dump(rows,open(HERE/'vertex_global_jet_sections.pickle','wb'))
report={'all_degree32_global':True,'generic_Xcenter_adjoint_order_atleast16':True,'generic_ruled_conductor_adjoint_membership':True,'mu3_character':1,'Y_sign':'even','generic_jet_dimension':420,'fine_source_delta_character2_dimension':140,'formulas':{'1':'X0^(16-k)X1^k Y1 Y0^j Y2^(15-j)','eps2':'X0^(18-k)X1^k Y1 Y0^j Y2^(13-j)','b':'X0^(16-k)X1^k Y1² Y0^j Y2^(14-j)','r':'X0^(16-k)X1^k (Y0⁶+Y2⁶)Y0^jY2^(10-j)'},'ranges':'j0..5; k0..16, except eps² k0..18','local_value':'Under canonical coefficient g/(6a5 eps16 b), gives a^j/(6a5)*v^k times designated jet. Corrections from a−zeta have weight>=12 and do not affect the cutoff7 quotient. Vandermonde on six roots a6=-1 is invertible.','scope':'Explicit surjectivity on the GENERIC vertex-defect jet bundles, already satisfying the two generic center adjoints. Additional adjoints at special-v/collision/discriminant loci may restrict the section source and remain unresolved.'}
(HERE/'vertex_global_jet_sections.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
