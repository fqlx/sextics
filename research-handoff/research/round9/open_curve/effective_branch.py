"""Exact branch factors of the source-specific effective marked cover."""
from pathlib import Path
import pickle,json,time,sympy as s
from flint import fmpq_mpoly_ctx,fmpq
HERE=Path(__file__).parent;start=time.monotonic()
d=pickle.loads(Path('/workspace/research/round9/abel_prym/effective_schiffer.pickle').read_bytes())
W,h,t,L,r,x,z=d['symbols'];ctx=fmpq_mpoly_ctx.get(('L','r','x','z'));ll,rr,xx,zz=ctx.gens();c=fmpq(5,7)
def native(f):return ctx.from_dict({tuple(map(int,e)):fmpq(str(coef))for e,coef in s.Poly(f,L,r,x,z).as_dict().items()})
N0,N1=native(d['N0']),native(d['N1'])
g=N0.gcd(N1);N0//=g;N1//=g
Bnum=xx*ll*N0**3+xx*rr*N1*N0*N0+N1**3
Dnum=c*c*xx*N0*(N0+N1)**2-4*Bnum
report={};payload={}
for name,f in [('B_effective_num',Bnum),('Delta_effective_num',Dnum)]:
 print('FACTOR',name,len(f.to_dict()),flush=True)
 con,factors=f.factor();replay=ctx.constant(con)
 for factor,mult in factors:replay*=factor**mult
 assert replay==f
 report[name]={'terms':len(f.to_dict()),'constant':str(con),'factors':[{'terms':len(q.to_dict()),'multiplicity':int(e),'degrees':list(map(int,q.degrees())),'factor':str(q)}for q,e in factors]}
 payload[name]={'constant':str(con),'factors':[{'dict':{tuple(map(int,a)):str(b)for a,b in q.to_dict().items()},'multiplicity':int(e)}for q,e in factors]}
 print(name,[(f['terms'],f['multiplicity'],f['degrees'])for f in report[name]['factors']],round(time.monotonic()-start,3),flush=True)
(HERE/'effective_branch.pickle').write_bytes(pickle.dumps(payload))
(HERE/'effective_branch.json').write_text(json.dumps({'factors':report,'exact_reconstruction':True,'seconds':time.monotonic()-start},indent=2)+'\n')
