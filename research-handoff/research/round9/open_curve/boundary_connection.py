"""Full rank5 open-curve connection: exact homogeneous boundary reductions."""
from pathlib import Path
import sympy as S,pickle,json,time
from sympy.polys.matrices import DomainMatrix
from flint import nmod_mat
HERE=Path(__file__).parent;start=time.monotonic()
data=pickle.loads(Path('/workspace/research/round9/cyclic_full/global_eta_complete.pickle').read_bytes())
W,h,t,L,r,x=data['symbols'];s=S.symbols('s');pars=(L,r,x,s);vv=(W,h,t);C=data['curve'];D=t-s*h*h
basis=data['basis'];sig=[h**4,W**3*h]
rows=[(a,b,c)for a in range(13)for b in range(13)for c in range(7)if a+b+2*c==12 and a%3==0]
def mon(e):return W**e[0]*h**e[1]*t**e[2]
labs=[(i,e)for i,wt,ch in [(0,5,1),(1,5,0),(2,6,0)]for e in [(a,b,c)for a in range(wt+1)for b in range(wt+1)for c in range(wt//2+1)if a+b+2*c==wt and a%3==ch]]
assert len(rows)==19 and len(labs)==16
# Every column represents its rational form with common denominator D²C².
cols=[basis[0]*D*D*C,basis[1]*D*D*C,basis[2]*D*D]+[n*D*C for n in sig]
for i,e in labs:
 q=mon(e);cols.append(C*D*S.diff(q,vv[i])-C*q*S.diff(D,vv[i])-D*q*S.diff(C,vv[i]))
A=S.Matrix.hstack(*[S.Matrix([S.Poly(S.expand(x*f),*vv).coeff_monomial(mon(e))for e in rows])for f in cols])
assert all(not S.denom(z).has(*pars) for z in A)
p=1000003;pt={L:1,r:2,x:3,s:4}
def md(f):
 v=S.Rational(f.subs(pt));return int(v.p)*pow(int(v.q),-1,p)%p
mod=nmod_mat([[md(A[i,j])for j in range(A.cols)]for i in range(A.rows)],p)
rref,rank=mod.rref();print('MODRANK',rank,flush=True)
piv=[]
for i in range(rank):piv.append(next(j for j in range(A.cols)if rref[i,j]))
assert len(piv)==len(set(piv))==rank
mt=nmod_mat([[md(A[i,j])for i in range(A.rows)]for j in piv],p)
rt,rkt=mt.rref();assert rkt==rank
rowpiv=[next(j for j in range(A.rows)if rt[i,j])for i in range(rank)]
for name,parameter in zip(['L','r','x','s'],pars):
 for n in sig:
  src=n*h*h*C if name=='s' else -n*S.diff(C,parameter)*D
  rhs=S.Matrix([S.Poly(S.expand(x*src),*vv).coeff_monomial(mon(e))for e in rows])
  aug=A.row_join(rhs)
  rk=nmod_mat([[md(aug[i,j])for j in range(aug.cols)]for i in range(aug.rows)],p).rank()
  print('AUGRANK',name,sig.index(n),rk,flush=True)
  assert rk==rank
print(json.dumps({'stage':'matrix','shape':A.shape,'pivot_columns':piv,'seconds':time.monotonic()-start}),flush=True)
AA=A[rowpiv,piv]
DM=DomainMatrix.from_Matrix(AA);iv,de=DM.inv_den();iv=iv.to_Matrix();de=DM.domain.to_sympy(de)
print(json.dumps({'stage':'inverted','seconds':time.monotonic()-start}),flush=True)
# Save the raw inverse before cancellation so an interruption loses no inversion.
(HERE/'boundary_inverse.pickle').write_bytes(pickle.dumps(dict(symbols=(*vv,*pars),A=A,pivot_columns=piv,inverse_numerator=iv,inverse_denominator=de,rows=rows,row_pivots=rowpiv,labs=labs)))
connection={};primitives={};checks=[]
for name,parameter in zip(['L','r','x','s'],pars):
 rr=[];qq=[]
 for j,n in enumerate(sig):
  source=n*h*h*C if name=='s' else -n*S.diff(C,parameter)*D
  rhs=S.Matrix([S.Poly(S.expand(x*source),*vv).coeff_monomial(mon(e))for e in rows])
  answer=[S.cancel(v/de)for v in iv*rhs[rowpiv,:]]
  full=[S.Integer(0)]*A.cols
  for i,v in zip(piv,answer):full[i]=v
  # Check exactly after clearing common denominators, using the same universal matrix.
  residual=A*S.Matrix(full)-rhs
  assert all(S.cancel(v)==0 for v in residual)
  rr.append(full[:5]);qq.append(full[5:]);checks.append((name,j))
  print(json.dumps({'stage':'row','direction':name,'boundary':j,'seconds':time.monotonic()-start}),flush=True)
 connection[name]=rr;primitives[name]=qq
packet=dict(symbols=(*vv,*pars),curve=C,graph=D,basis=basis+sig,basis_denominators=['C','C','C²','D*C','D*C'],connection_boundary=connection,primitive_coefficients=primitives,primitive_labels=labs,primitive_convention='Each derivative equals connection row times basis + d_curve((QW-W*Qh)/(D*C_t)); Q assembled from primitive_coefficients/labels.',exact_coefficient_checks=checks,pivot_columns=piv,seconds=time.monotonic()-start)
(HERE/'boundary_connection.pickle').write_bytes(pickle.dumps(packet))
(HERE/'boundary_connection.json').write_text(json.dumps(dict(exact_rows=checks,pivot_columns=piv,basis=['h²/C','t/C','eta_new/C²','h4/(D*C)','W3h/(D*C)'],primitive_convention=packet['primitive_convention'],seconds=time.monotonic()-start),indent=2)+'\n')
print('DONE',flush=True)
