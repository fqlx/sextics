from pathlib import Path
import json
from flint import fmpq_mpoly_ctx,fmpq_mpoly
p=Path(__file__).parent
c=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=c.gens();z=c.constant(0)
P=lambda t:fmpq_mpoly(t.replace('**','^'),c)
r=json.loads((p/'j-source-primitive-results.json').read_text());ij=json.loads((p/'rank8-ij-connections-results.json').read_text());vv=json.loads((p/'rank8-v-literal-primitives-results.json').read_text())
Gi=[[P(x)for x in row]for row in ij['full_rank9_Gamma_numerators']['i']];Gj=[[P(x)for x in row]for row in ij['full_rank9_Gamma_numerators']['j']];GV=[[P(x)for x in row]for row in vv['full_rank9_GammaV_numerators']];d=P(ij['common_denominator']);dv=P(vv['common_denominator'])
W=[P(t)for t in r['Wbq_polynomial_vector']]+[z];U=[P(t)for t in r['U_numerators']]+[z];Ui=[z,z,j/6,z,z,z,c.constant(2)/3,i/3,z]
V=[P(t)for t in json.loads((p.parent.parent/'theta-compact/mixed-i-primitive-results.json').read_text())['compact_vector']]+[z]
def calc(A,vec,der,den):
 out=[]
 for rr in range(9):
  num=den*der(vec[rr])+sum((a*b for a,b in zip(A[rr],vec)),z)
  cc=den.gcd(num);nn=num//cc;dd=den//cc
  if dd.degrees()==(0,0,0):nn=nn/dd.to_dict()[(0,0,0)];dd=c.constant(1)
  out.append({'n':str(nn),'d':str(dd)})
 return out
out={}
for name,vec in [('W',W),('U',U),('Ui',Ui),('Vi',V)]:
 for ds,A,den,der in [('i',Gi,d,lambda x:x.derivative(0)),('j',Gj,d,lambda x:x.derivative(1)),('V',GV,dv,lambda x:6*v*x.derivative(2))]:
  rr=calc(A,vec,der,den);out[name+'_'+ds]=rr
  print(name,ds,'polynomial',all(t['d']=='1'for t in rr))
  if all(t['d']=='1'for t in rr):print([t['n']for t in rr])
(p/'polynomial-potential-rows-results.json').write_text(json.dumps(out,indent=2)+'\n')
