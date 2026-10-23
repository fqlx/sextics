"""Exact physical branch factors of the source-specific marked cover."""
from pathlib import Path
import pickle,json,time
from flint import fmpq,fmpq_mpoly_ctx
HERE=Path(__file__).parent;start=time.monotonic()
data=pickle.loads(Path('/workspace/research/round9/abel_prym/effective_physical.pickle').read_bytes())['t_old_over_h2']
ctx=fmpq_mpoly_ctx.get(('a','b','v'));a,b,v=ctx.gens();c=fmpq(5,7)
def poly(d):return ctx.from_dict({e:fmpq(k)for e,k in d.items()})
N,D=poly(data['num']),poly(data['den'])
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
H=P*D**3+Q*N*D**2+R*N**2*D+S*N**3
Delta=c*c*D*(D+B*N)**2-4*H
print('BUILT',len(H.to_dict()),len(Delta.to_dict()),round(time.monotonic()-start,3),flush=True)
def payload(f):return{tuple(map(int,e)):str(c)for e,c in f.to_dict().items()}
(HERE/'physical_branch_raw.pickle').write_bytes(pickle.dumps({'variables':('a','b','v'),'N':payload(N),'D':payload(D),'Hnum':payload(H),'DeltaNum':payload(Delta)}))
report={};pack={}
for name,f in [('Hnum',H),('DeltaNum',Delta)]:
 print('FACTOR',name,flush=True)
 con,fac=f.factor();replay=ctx.constant(con)
 for q,e in fac:replay*=q**e
 assert replay==f
 report[name]={'terms':len(f.to_dict()),'degrees':list(map(int,f.degrees())),'constant':str(con),'factors':[{'terms':len(q.to_dict()),'degrees':list(map(int,q.degrees())),'multiplicity':int(e),'factor':str(q)if len(q.to_dict())<100 else '(large factor; see pickle)'}for q,e in fac]}
 pack[name]={'constant':str(con),'factors':[{'polynomial':payload(q),'multiplicity':int(e)}for q,e in fac]}
 print(name,[(len(q.to_dict()),int(e),list(map(int,q.degrees())))for q,e in fac],round(time.monotonic()-start,3),flush=True)
 (HERE/'physical_branch_partial.json').write_text(json.dumps(report,indent=2)+'\n')
common=H.gcd(Delta);report['gcd']={'terms':len(common.to_dict()),'degrees':list(map(int,common.degrees())),'factor':str(common)if len(common.to_dict())<100 else '(large factor; see pickle)'};pack['gcd']=payload(common)
(HERE/'physical_branch.pickle').write_bytes(pickle.dumps(pack))
(HERE/'physical_branch.json').write_text(json.dumps({'exact_reconstructions':True,'report':report,'seconds':time.monotonic()-start},indent=2)+'\n')
print('DONE',round(time.monotonic()-start,3),flush=True)
