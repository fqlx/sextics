"""Source-forced nullflow boundary2form: exact finite-field jet test.
The quadratic trace forces a rational eta-matched seed; closedness is retained.
"""
from pathlib import Path
import sys,pickle,json,time
HERE=Path(__file__).parent;sys.path.insert(0,'/workspace/research/round10/horizontal5')
from physical_search import OpenModel,Jet,qmod,dot
import importlib.util
spec=importlib.util.spec_from_file_location('horizontal_log_search','/workspace/research/round10/horizontal5/log_search.py');logs=importlib.util.module_from_spec(spec);spec.loader.exec_module(logs);physical_second=logs.physical_second
from jet2 import Jet2,evaluate
start=time.monotonic();p=1000003
model=OpenModel(p,'/workspace/research/round10/horizontal5/rank5_connection.pickle');Jet.p=p;Jet2.p=p
records=[]
for pt in [[1,2,3],[2,1,3],[2,3,1],[3,4,2]]:
 d=model.point(pt);pars,s=physical_second(model,d);L,r,x=[Jet(q.x,q.d)for q in pars];mark=Jet(s.x,s.d);c=qmod('5/7',p)
 flow=[x*((c*c-10*r)*L+4*r*r),x*r*(c*c-5*r)-18*L+9*r,-x*((c*c+5*r)*x+27)]
 V=[]
 for j in range(3):
  row=[]
  for a in range(3):
   grad=[-sum(d['fields'][m][a]*pars[m].h[n][b]*d['fields'][j][n] for m in range(3)for n in range(3))%p for b in range(3)]
   row.append(Jet(d['fields'][j][a],grad))
  V.append(row)
 delta=[sum((flow[j]*V[j][a]for j in range(3)),Jet(0))for a in range(3)];dv=[v.x for v in delta]
 ds=sum((delta[a]*Jet(s.d[a],s.h[a])for a in range(3)),Jet(0))
 A=c*(1+mark);B=L+r*mark+mark**3/x;Delta=A*A-4*B
 K=r*(5*mark+4)+3*mark*(2*mark+3)/x;D0=ds/x+K;NF=D0*D0-c*A*D0+c*c*B
 def evpair(pair):return evaluate(pair[0],pars)/evaluate(pair[1],pars)
 NR12=evpair(model.proper.conn[1][5]);NR02=evpair(model.proper.conn[1][2]);NL02=evpair(model.proper.conn[0][2])
 # z is supplied by the independent physical source quotient model.
 z=d['z'];Seta=-Jet(NR12.x,NR12.d)+2*z*Jet(NR02.x,NR02.d)-z*z*Jet(NL02.x,NL02.d)
 assert Seta.x==d['rhs'][2]
 Z=[-7*Seta*Delta*c*B/(2*NF),-7*Seta*Delta*D0/(2*NF)]
 NN=[[sum(dv[a]*d['openphysical'][a][i][j]for a in range(3))%p for j in range(5)]for i in range(5)]
 E=[NN[3][2],NN[4][2]];assert dot(E,[z.x for z in Z],p)==Seta.x
 divcan=(-30*r.x*x.x-18)%p;charge=(dot(dv,d['logH'],p)+divcan)%p
 closure=[(dot(dv,Z[j].d,p)+charge*Z[j].x+sum(NN[i+3][j+3]*Z[i].x for i in range(2)))%p for j in range(2)]
 properimage=[sum(NN[i+3][j]*Z[i].x for i in range(2))%p for j in range(3)]
 remaining=[(d['rhs'][j]-properimage[j])%p for j in range(3)]
 assert remaining[2]==0
 records.append({'physical_point':pt,'parameters':d['pars'],'s':mark.x,'delta_s':ds.x,'D0':D0.x,'NF':NF.x,'S_eta':Seta.x,'Z':[z.x for z in Z],'delta_Z':[dot(dv,z.d,p)for z in Z],'charge_plus_div':charge,'eta_match_exact_at_point':True,'residue_closedness_defect':closure,'remaining_proper_hol_source':remaining[:2]})
out={'prime':p,'candidate':'Z=-7*S_eta*Delta/(2*NF)*(c*B,D0), D0=delta(s)/x+K,NF=D0²-c*A*D0+c²B; current rho*fT*Z along physical delta','records':records,'closed_at_all_points':all(not any(q['residue_closedness_defect'])for q in records),'scope':'One explicitly forced quadratic-trace nullflow boundary seed. Nonzero defect rejects this seed only; arbitrary residueclosed boundary2forms and general rank5 currents remain open.','seconds':time.monotonic()-start}
(HERE/'forced_nullflow.json').write_text(json.dumps(out,indent=2,default=int)+'\n');print(json.dumps(out,indent=2,default=int))
