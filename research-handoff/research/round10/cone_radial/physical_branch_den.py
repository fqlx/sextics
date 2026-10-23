from pathlib import Path
import pickle,json,time
from flint import fmpq,fmpq_mpoly_ctx
HERE=Path(__file__).parent;start=time.monotonic();ctx=fmpq_mpoly_ctx.get(('a','b','v'))
data=pickle.loads((HERE/'physical_branch_raw.pickle').read_bytes())
polys={name:ctx.from_dict({e:fmpq(c)for e,c in data[name].items()})for name in ['N','D','Hnum','DeltaNum']}
reports={};pack={}
for name in ['N','D']:
 f=polys[name];con,fac=f.factor();replay=ctx.constant(con)
 for q,e in fac:replay*=q**e
 assert replay==f
 reports[name]={'constant':str(con),'factors':[{'multiplicity':int(e),'degrees':list(map(int,q.degrees())),'terms':len(q.to_dict()),'factor':str(q)if len(q.to_dict())<100 else '(large factor; see pickle)'}for q,e in fac]}
 pack[name]={'constant':str(con),'factors':[{'multiplicity':int(e),'polynomial':{tuple(map(int,a)):str(b)for a,b in q.to_dict().items()}}for q,e in fac]}
reports['gcd_H_D']=str(polys['Hnum'].gcd(polys['D']));reports['gcd_Delta_D']=str(polys['DeltaNum'].gcd(polys['D']))
(HERE/'physical_branch_den.pickle').write_bytes(pickle.dumps(pack));(HERE/'physical_branch_den.json').write_text(json.dumps({'report':reports,'seconds':time.monotonic()-start},indent=2)+'\n');print((HERE/'physical_branch_den.json').read_text())
