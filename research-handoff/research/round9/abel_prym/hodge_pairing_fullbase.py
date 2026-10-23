"""Test the full-base polarization/marked-point relation, keeping gauge defects."""
from pathlib import Path
import pickle,json,time,sympy as s,resource
HERE=Path(__file__).parent;start=time.monotonic();resource.setrlimit(resource.RLIMIT_CPU,(85,90))
q=pickle.load(open(HERE.parent/'cyclic_full'/'conjugate_fast.pickle','rb'));bp=pickle.load(open(HERE.parent/'open_curve'/'boundary_native.pickle','rb'))
W,h,T,L,r,x=q['symbols'];sp=s.symbols('s');c=s.Rational(5,7);A=c*(1+sp);C=q['curve'];ct=s.diff(C,T);cw=s.diff(C,W)
Lmark=-W**6-c*(1+sp)*W**3-r*sp-sp**3/x

def expr(pp):
 def poly(d):return sum(s.Rational(cc)*L**e[0]*r**e[1]*x**e[2]*sp**e[3]for e,cc in d.items())
 return poly(pp['numerator'])/poly(pp['denominator'])
result={}
for name in('s','L','r','x'):
 u=0
 if name!='s':
  pp=q['primitives'][name][0]
  for co,(component,ex)in zip(pp['Q8_raw'],q['lab8']):
   if component not in(0,1):continue
   u+=(-1 if component==1 else 1)*co/pp['Q8_denominator']*W**(ex[0]+int(component==1))*T**ex[2]
 ci=ct if name=='s'else s.diff(C,{'L':L,'r':r,'x':x}[name])
 alpha=(-W*ci/cw+u)/ct
 alpha=alpha.subs({h:1,T:sp})
 eta=[expr(bp['connection_boundary'][name][j][2])for j in(0,1)]
 pair=W**2*((-A-W**3)*eta[0]-eta[1])*7*x/18
 defect=s.factor(s.cancel((pair+alpha/6).subs(L,Lmark)))
 result[name]={'zero':defect==0,'defect':str(defect)}
 print(name,defect==0,time.monotonic()-start,flush=True)
report={'directions':result,'relation_tested':'<nabla theta_chi,omega_conj>/(1-zeta^2)+alpha_conj(P)/6','scope':'Records whether the chosen rational splitting has the simple marked-point relation off the isoperiodic flow. Nonzero terms are splitting/gauge defects and are not treated as source obstructions.','seconds':time.monotonic()-start}
(HERE/'hodge_pairing_fullbase.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
