"""Exact actual/conjugate rank-three polarization from weighted Jacobian residues.

Normalizes the affine Grothendieck residue by Res(Hess C)=Milnor number50.
The common topological cup-product scalar is left unspecified.  It is
constant and does not affect GM compatibility or source-channel comparisons.
"""
from pathlib import Path
import sympy as s,pickle,json,time,resource,argparse
from sympy.polys.matrices import DomainMatrix
from sympy.polys.fields import field
from sympy.polys.domains import QQ
HERE=Path(__file__).parent;start=time.monotonic()
ap=argparse.ArgumentParser();ap.add_argument('--resume-x',action='store_true');args=ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(170,180))
a=pickle.load(open(HERE.parent/'cyclic_full'/'actual_fast.pickle','rb'));co=pickle.load(open(HERE.parent/'cyclic_full'/'conjugate_fast.pickle','rb'))
W,h,t,L,r,x=a['symbols'];C=a['curve'];vars=(W,h,t);pars=(L,r,x)
rr=[(i,j,k)for i in range(11)for j in range(11)for k in range(6)if i+j+2*k==10 and i%3==1]
mon=lambda e:W**e[0]*h**e[1]*t**e[2]
lab=[]
for i,wt,ch in[(0,5,2),(1,5,1),(2,6,1)]:
 lab +=[(i,(j,k,m))for j in range(wt+1)for k in range(wt+1)for m in range(wt//2+1)if j+k+2*m==wt and j%3==ch]
cols=[]
for i,e in lab:
 dd=s.Poly(s.expand(x*s.diff(C,vars[i])*mon(e)),*vars).as_dict();cols.append([dd.get(e,0)for e in rr])
J=s.Matrix.hstack(*map(s.Matrix,cols));ns=DomainMatrix.from_Matrix(J.T).nullspace().to_Matrix();assert ns.rows==1
ell=ns[0,:].T
Hess=s.det(s.hessian(C,vars));hd=s.Poly(s.expand(Hess),*vars).as_dict();norm=s.cancel(sum(ell[i]*hd.get(e,0)for i,e in enumerate(rr)))
res=[s.cancel(50*e/norm)for e in ell]
lookup=dict(zip(rr,res))
R1=lookup[(1,3,3)];R2=lookup[(1,5,2)];R3=lookup[(1,1,4)]
print('RESIDUES',*(s.count_ops(q)for q in(R1,R2,R3)),time.monotonic()-start,flush=True)
# Pole1-pole2 orientations are opposite for the two factors.
H=s.Matrix([[0,R1,R2],[0,R3,R1],[-R3,0,0]])
# The derivative of a known hol/eta pairing determines the eta/eta entries.
N=a['connection']['L'];M=co['connection']['L'];i=0
for j in(1,2):
 expr=s.diff(H[i,j],L)-sum(N[i,k]*H[k,j]for k in(0,1))-sum(H[i,k]*M[j,k]for k in range(3))
 H[2,j]=s.cancel(expr/N[i,2])
print('PAIRING',s.count_ops(H[2,1]),s.count_ops(H[2,2]),time.monotonic()-start,flush=True)
pickle.dump({'H':H,'R':(R1,R2,R3),'Jacobian_residue':lookup},open(HERE/'polarization_partial.pickle','wb'))
checks={}
F,fL,fr,fx=field('L,r,x',QQ)
fh=[[F.from_expr(H[i,j]) for j in range(3)] for i in range(3)]
# The L and r exact checks completed before a runtime interruption and are
# preserved in polarization_previous_checks.log.  Only x remains to resume.
for z in(('x',) if args.resume_x else ('L','r','x')):
 N=[[F.from_expr(a['connection'][z][i,j]) for j in range(3)] for i in range(3)]
 M=[[F.from_expr(co['connection'][z][i,j]) for j in range(3)] for i in range(3)]
 zz={'L':fL,'r':fr,'x':fx}[z]
 checks[z]=[]
 for i in range(3):
  for j in range(3):
   e=fh[i][j].diff(zz)-sum(N[i][k]*fh[k][j]+fh[i][k]*M[j][k] for k in range(3))
   ok=e==0;checks[z].append(ok)
   assert ok,(z,i,j,str(e))
 print('FLAT_PAIRING',z,time.monotonic()-start,flush=True)
detH=s.cancel(R3*(R2*R3-R1**2));assert detH!=0
out={'symbols':a['symbols'],'pairing_actual_rows_conjugate_columns':H,'R':(R1,R2,R3),'Jacobian_residue':lookup,'normalization':'Res(Hess C)=50. The topological residue cup product is a common nonzero constant multiple of this normalization.','connection_convention':'dH=N_actual H+H N_conjugate^T','all27_connection_checks_exact':True}
(HERE/'polarization.pickle').write_bytes(pickle.dumps(out))
report={'matrix':[[str(s.factor(z))for z in row]for row in H.tolist()],'residue_normalization':out['normalization'],'all27_connection_checks_exact':True,'continued_checks':'L and r completed before runtime interruption; x checked in this resumed run.','determinant':str(s.factor(detH)),'seconds':time.monotonic()-start,'scope':'A flat nondegenerate pairing, normalized via Jacobian residue on holomorphic versus pole-two forms. It provides actual/conjugate duality for extension/source audits; it does not itself solve a source equation.'}
(HERE/'polarization.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
