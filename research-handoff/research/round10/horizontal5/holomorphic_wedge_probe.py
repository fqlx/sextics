"""Test small wedges of the two corrected actual holomorphic lifts.
These are potential nonexact forms, not arbitrary coefficient sweeps.
"""
import sys,pickle,json,sympy as sy
from pathlib import Path
from flint import nmod_poly
sys.path.insert(0,'/workspace/research/round9/marked_log_module')
from physical import J1,J2,Poly,PhysicalModel,qmod
P=1009;J1.p=J2.p=P;M=PhysicalModel(P);data=pickle.load(open('/workspace/research/round9/cyclic_full/actual_fast.pickle','rb'));W,h,T,L,r,x=data['symbols']
polys={}
for name in ('L','r','x'):
 for i in (0,1):
  primitive=data['primitives'][name][i];Qaff=0
  for k,(comp,ex)in enumerate(data['lab8']):
   if comp in (0,1):Qaff+=(-1 if comp==1 else 1)*primitive['Q8_raw'][k]*W**(ex[0]+int(comp==1))*T**ex[2]
  f=sy.cancel(Qaff/primitive['Q8_denominator']);nn,dd=sy.fraction(f)
  polys[name,i]=(Poly(sy.Poly(nn,W,T,L,r,x).as_dict(),P),Poly(sy.Poly(dd,W,T,L,r,x).as_dict(),P))
records=[]
for pt in ([1,2,3],[1,3,2],[8,9,2]):
 a,b,v=[J2(pt[i],seed=i)for i in range(3)];c=qmod('5/7',P);B=b*(1+a*v);PP=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
 LL=(27*PP*S*S-9*Q*R*S+2*R**3)/(3*A*A);rr=(3*S*Q-R*R)/(B*A);xx=3*B**3/A;z=B*R/A
 mark=M.evaluate(M.Te,[LL,rr,xx,z]);pars=[LL,rr,xx];aa=c*(1+mark);bb=LL+rr*mark+mark**3/xx
 f=nmod_poly([bb.c[0],0,0,aa.c[0],0,0,1],P);roots=[(-int(g[0])*pow(int(g[1]),-1,P))%P for g,e in f.factor()[1]if g.degree()==1]
 for w0 in roots[:1]:
  w=J2(w0)
  for _ in range(3):w-=(w**6+aa*w**3+bb)/(6*w**5+3*aa*w**2)
  assert not any((w**6+aa*w**3+bb).c)
  args=[j.first()for j in [w,mark,LL,rr,xx]];ct=(c*w**3+rr+3*mark**2/xx).first();hol=[]
  for i in (0,1):
   corr=[M.evaluate(polys[name,i],args)for name in ('L','r','x')];nu=J1(1)if i==0 else mark.first()
   hol.append([(nu*w.derivative(k)+sum((corr[j]*pars[j].derivative(k)for j in range(3)),J1()))/ct for k in range(3)])
  al,be=hol;wed=[al[1]*be[2]-al[2]*be[1],al[2]*be[0]-al[0]*be[2],al[0]*be[1]-al[1]*be[0]]
  U=w.first()**3;AA=aa.first();BB=bb.first();DD=2*U+AA
  scalars={'1':J1(1),'w2':w.first()**2,'1/w':1/w.first(),'w2/delta_root':w.first()**2/DD,'1/(w*delta_root)':1/(w.first()*DD),'w2/B':w.first()**2/BB,'1/(w*B)':1/(w.first()*BB)}
  defects={name:sum((f*wed[i]).g[i]for i in range(3))%P for name,f in scalars.items()}
  records.append(dict(point=pt,w=w0,closure_defects=defects))
out={'prime':P,'records':records,'scope':'Bounded natural scalar multiples of corrected holomorphic-lift wedge only. Nonzero defect excludes that candidate, not global H20.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
