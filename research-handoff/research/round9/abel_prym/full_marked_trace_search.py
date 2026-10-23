#!/usr/bin/env python3
"""24 traced currents from every marked-point de Rham form in both characters.

The higher-pole absolute primitive convention is independently audited in
higher_pole_audit.py. These sampled modules are constructive searches only.
"""
import sys,json,pickle,time,argparse,random
from pathlib import Path
import sympy as sy
from flint import nmod_mat
HERE=Path(__file__).parent
sys.path.insert(0,str(HERE.parent/'coupled_search'))
from search import Model,Jet,Poly,qmod,dot,monomials
from marked_trace_search import J2,Quad,ratiojet,columns

def compile_full(p):
 out=[]
 for name,char in [('actual',1),('conjugate',2)]:
  data=pickle.load(open(HERE.parent/'cyclic_full'/f'{name}_fast.pickle','rb'));variables=data['symbols'][3:]
  def comp(f):
   n,d=sy.fraction(f);return Poly(sy.Poly(n,*variables).as_dict(),p),Poly(sy.Poly(d,*variables).as_dict(),p)
  for idx in range(3):
   directions=[]
   for direction in('L','r','x'):
    pp=data['primitives'][direction][idx];degrees={}
    for degree in(8,14):
     raw=pp[f'Q{degree}_raw']
     if raw is None:continue
     terms=[]
     for coeff,(component,e)in zip(raw,data[f'lab{degree}']):
      if component not in(0,1)or coeff==0:continue
      power=e[0]+int(component==1)
      assert(power-char)%3==0 and power>=char
      terms.append((comp(coeff),1 if component==0 else -1,(power-char)//3,e[2]))
     degrees[degree]=(terms,comp(pp[f'Q{degree}_denominator']))
    directions.append(degrees)
   ex=sy.Poly(data['basis'][idx],*data['symbols'][:3]).monoms()[0]
   assert ex[0]==char-1
   out.append((name,idx,char,data['basis_pole_orders'][idx],ex[2],directions))
 return out

def full_fields(model,pt,compiled):
 p=model.p;J2.p=p;point=model.point(pt)
 a=J2(pt[0],[1,0]);b=J2(pt[1],[0,1]);v=J2(pt[2]);c=qmod('5/7',p)
 E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R;M=A/(3*S)
 L=(27*P*S**2-9*Q*R*S+2*R**3)/(3*A**2);r=(3*S*Q-R**2)/(B*A);x=3*B**3/A;z=B*R/A;pars=[L,r,x]
 assert[t.x for t in pars]==point['pars']
 logRho=[(A.derivative(i)/A.jet()-S.derivative(i)/S.jet())/3 for i in range(2)]
 Quad.c=Jet(c);Quad.P=P.jet();u=Quad(0,1);ct=c*u/M.jet()+r.jet()+3*z.jet()**2/x.jet();ctt=6*z.jet()/x.jet();um=u/M.jet()
 basic=[]
 for name,idx,char,pole,et,directions in compiled:
  rel=Quad(z.jet()**et)/ct
  if pole==2:rel=(ct*(et*z.jet()**(et-1))-z.jet()**et*ctt)/ct**3
  corr=[]
  for degrees in directions:
   values={}
   for degree,(terms,den)in degrees.items():
    value=Quad(0);dtvalue=Quad(0)
    for pair,sign,q,k in terms:
     base=sign*Quad(ratiojet(pair,pars))*um**q
     value+=base*z.jet()**k
     if k:dtvalue+=base*k*z.jet()**(k-1)
    denval=ratiojet(den,pars);values[degree]=(value/denval,dtvalue/denval)
   f=values[8][0]/ct
   if 14 in values:f+=(values[14][1]*ct-values[14][0]*ctt)/ct**3
   corr.append(f)
  ri=[]
  for i in(0,1):ri.append(-rel*logRho[i]+sum((corr[j]*pars[j].derivative(i)for j in range(3)),Quad(0)))
  for j in range(3 if name=='actual'else 4):basic.append((f'{name}{idx}_v{j}',[ri[1].b*pow(pt[2],j,p),-ri[0].b*pow(pt[2],j,p),Jet(0)]))
  if name=='conjugate':basic.append((f'{name}{idx}_u',[ri[1].a-c*ri[1].b,-ri[0].a+c*ri[0].b,Jet(0)]))
 assert len(basic)==24
 point['markedfields']=basic;point['fT']=3*a.jet()**3*S.jet()/(2*B.jet()**3*A.jet())
 return point

def labels(degree,zmax,components,densities):
 out=[];seen=set()
 groups=[i for i in range(3)for _ in range(3)]
 vpowers=list(range(3))*3
 for i in range(3):groups+=([3+i]*4+[6+i]);vpowers+=list(range(4))+[0]
 for density in densities:
  for j in range(24):
   for c in range(components):
    for k in range(zmax+1):
     for e in monomials(degree):
      key=(density,groups[j],c,k,e[0],e[1],e[2]+vpowers[j])
      if key not in seen:seen.add(key);out.append((j,c,e,k,density))
 return out

def run(args):
 start=time.monotonic();p=args.prime;rng=random.Random(args.seed);model=Model(p,args.basis);compiled=compile_full(p)
 labs=labels(args.degree,args.zmax,args.components,args.densities.split(','));n=len(labs);samples=args.samples or n//3+35
 rows=[];rhs=[];pts=[];nonzero=[False]*24
 while len(pts)<samples:
  pt=[rng.randrange(1,p)for _ in range(3)]
  try:d=full_fields(model,pt,compiled);rr=columns(d,labs,p)
  except(ZeroDivisionError,ValueError):continue
  rows.extend(rr);rhs.extend(d['correction']if args.correction else d['rhs']);pts.append(pt)
  for j,(_,f)in enumerate(d['markedfields']):nonzero[j]|=any(q.x for q in f)
 print(json.dumps({'stage':'matrix','columns':n,'rows':len(rows),'nonzero24':nonzero,'seconds':time.monotonic()-start}),flush=True)
 rank=nmod_mat(rows,p).rank();RR,arank=nmod_mat([row+[y]for row,y in zip(rows,rhs)],p).rref();sol=None;validation=None
 if rank==arank:
  sol=[0]*n
  for i in range(arank):
   pivot=next((j for j in range(n)if RR[i,j]),None)
   if pivot is not None:sol[pivot]=int(RR[i,n])
  validation=True
  for _ in range(20):
   while True:
    pt=[rng.randrange(1,p)for _ in range(3)]
    try:d=full_fields(model,pt,compiled);rr=columns(d,labs,p);break
    except(ZeroDivisionError,ValueError):pass
   if any(dot(row,sol,p)!=y for row,y in zip(rr,d['correction']if args.correction else d['rhs'])):validation=False;break
 result={'args':vars(args),'columns':n,'rows':len(rows),'rank':rank,'augmented_rank':arank,'nonzero24':nonzero,'validation20':validation,'seconds':time.monotonic()-start,'scope':'Sampled full coupled current module generated by all24 marked de Rham traceforms. No arbitrary-current exclusion, direct Gysin serving claim, or source certificate.'}
 stem=HERE/args.output;pickle.dump(dict(result=result,labels=labs,points=pts,solution=sol),open(str(stem)+'.pickle','wb'));Path(str(stem)+'.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=0);ap.add_argument('--zmax',type=int,default=0);ap.add_argument('--components',type=int,choices=(2,3),default=3);ap.add_argument('--densities',default='rho,rhofT');ap.add_argument('--basis',choices=('eta','theta'),default='eta');ap.add_argument('--samples',type=int,default=0);ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--seed',type=int,default=9557);ap.add_argument('--output',default='full24_constant');ap.add_argument('--correction',action='store_true');run(ap.parse_args())
