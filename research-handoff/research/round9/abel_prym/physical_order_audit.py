"""Exact affine squarefree checks and projective boundary valuations of the rank6 order."""
from pathlib import Path
import pickle,json,time,resource
from flint import fmpq_mpoly_ctx,fmpq
HERE=Path(__file__).parent;start=time.monotonic();resource.setrlimit(resource.RLIMIT_CPU,(55,60))
ctx=fmpq_mpoly_ctx.get(('a','b','v'));a,b,v=ctx.gens();c=fmpq(5,7)
p=pickle.load(open(HERE/'effective_physical.pickle','rb'))['t_old_over_h2']
load=lambda d:ctx.from_dict({e:fmpq(cc)for e,cc in d.items()})
n,d=load(p['num']),load(p['den']);B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
alpha=c*(d+B*n);beta=P*d**3+Q*d*d*n+R*d*n*n+S*n**3;delta=alpha*alpha*d-4*beta
polys={'d':d,'n':n,'alpha':alpha,'beta':beta,'delta':delta}
def meta(f,expected):
 dd=f.to_dict();yg=max(e[0]+e[1]for e in dd);xg=max(e[2]for e in dd)
 return{'terms':len(dd),'actual_bidegree_Y_X':[yg,xg],'expected_bidegree':expected,'Y2_valuation':expected[0]-yg,'X0_valuation':expected[1]-xg}
expected={'d':[15,17],'n':[13,19],'alpha':[15,20],'beta':[45,57],'delta':[45,57]}
report={'metadata':{k:meta(f,expected[k])for k,f in polys.items()},'checks':{},'seconds':time.monotonic()-start}
(HERE/'physical_order_partial.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
for name in('d','beta','delta'):
 f=polys[name];g=f
 for i in range(3):g=g.gcd(f.derivative(i))
 report['checks'][name+'_affine_squarefree']=g.is_constant()
 print('SQUAREFREE',name,g.is_constant(),time.monotonic()-start,flush=True)
 assert g.is_constant()
for k,j in(('d','n'),('d','beta'),('beta','delta')):
 g=polys[k].gcd(polys[j]);report['checks'][k+'_'+j+'_affine_coprime']=g.is_constant()
 print('COPRIME',k,j,g.is_constant(),time.monotonic()-start,flush=True)
 assert g.is_constant()
report.update({'seconds':time.monotonic()-start,'scope':'Exact affine good-branch normality checks plus precise coordinate-boundary valuations. Global normality requires separate treatment of every nonzero boundary valuation; codimension2 singularities require resolution analysis even if order normality holds.'})
(HERE/'physical_order_audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
