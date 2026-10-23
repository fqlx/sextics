"""Probe Frobenius integrability of the marked conjugate Hodge oneform.
Nonzero reduction proves nonintegrability of this line; no H20 exclusion.
"""
from pathlib import Path
import pickle,sys,json
from flint import nmod_poly,fmpq_mpoly_ctx,fmpq_mpoly
sys.path.insert(0,'/workspace/research/round9/marked_log_module')
from physical import J1,J2,Poly,qmod,PhysicalModel
P=1009;J1.p=J2.p=P;M=PhysicalModel(P);ctx=fmpq_mpoly_ctx.get(('L','r','x','s'))
p=pickle.load(open('/workspace/research/round10/horizontal5/rank5_connection.pickle','rb'))
def pair(e):return(Poly(fmpq_mpoly(e['numerator'],ctx).to_dict(),P),Poly(fmpq_mpoly(e['denominator'],ctx).to_dict(),P))
E={k:[[pair(p['connection'][k][i][2])for i in (3,4)]][0]for k in ('L','r','x','s')}
records=[]
for pt in ([1,2,3],[2,3,5],[3,4,7],[1,3,2],[4,2,3],[7,5,2],[8,9,2]):
 try:
  a,b,v=[J2(pt[i],seed=i)for i in range(3)];c=qmod('5/7',P);B=b*(1+a*v);PP=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
  L=(27*PP*S*S-9*Q*R*S+2*R**3)/(3*A*A);rr=(3*S*Q-R*R)/(B*A);x=3*B**3/A;z=B*R/A
  mark=M.evaluate(M.Te,[L,rr,x,z]);pars=[L,rr,x,mark];args=[j.first()for j in pars];aa=c*(1+mark.first());bb=(L+rr*mark+mark**3/x).first()
  f=nmod_poly([bb.v,0,0,aa.v,0,0,1],P);roots=[(-int(g[0])*pow(int(g[1]),-1,P))%P for g,e in f.factor()[1]if g.degree()==1]
  if not roots:continue
  for w0 in roots[:2]:
   cw=3*w0*w0*(2*pow(w0,3,P)+aa.v)%P
   w=J1(w0,[-(pow(w0,3,P)*aa.g[i]+bb.g[i])*pow(cw,-1,P)%P for i in range(3)])
   U=w**3;other=-aa-U;expr=[M.evaluate(E[name][0],args)*other-M.evaluate(E[name][1],args)for name in E]
   alpha=[-qmod('7/3',P)*x.first()*w*w*sum((expr[j]*pars[j].derivative(i)for j in range(4)),J1())for i in range(3)]
   curl=[alpha[2].g[1]-alpha[1].g[2],alpha[0].g[2]-alpha[2].g[0],alpha[1].g[0]-alpha[0].g[1]]
   contact=sum(alpha[i].v*curl[i]for i in range(3))%P
   records.append(dict(point=pt,marked_w=w0,alpha=[f.v for f in alpha],contact_coefficient=contact))
 except (ZeroDivisionError,ValueError):continue
out={'prime':P,'records':records,'nonintegrable':any(v['contact_coefficient']for v in records),'scope':'Marked conjugate Hodge1form defined by full boundary eta coupling and exact clean polarization; Frobenius test only, no all-source or global H20 exclusion.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
