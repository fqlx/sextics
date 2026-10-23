from pathlib import Path
import sympy as sp,pickle,json
root=Path(__file__).parent;P=pickle.load(open(root/'legendre_model.pickle','rb'));G=pickle.load(open('/workspace/research/round6/k3_normalform/lambda_gm.pickle','rb'))
q,h,sl,ti,v,k=[P['symbols'][n]for n in ['q','h','s','t','v','k']]
p=103;point={q:1,h:4,sl:13,ti:67,v:18,P['ell']:57};base={q:1,h:4};ell=57
def mod(x):
 x=sp.cancel(x);return int(x.p)%p*pow(int(x.q)%p,-1,p)%p
E=P['equations'];J=sp.Matrix([[mod(sp.diff(e,z).subs(point))for z in [sl,ti,v]]for e in E]);Ji=J.inv_mod(p)
dpar={}
for var in [q,h]:
 d=Ji*sp.Matrix([-mod(sp.diff(e,var).subs(point))for e in E]);dpar[var]=[int(x)%p for x in d]
sv,tv,vv=[point[z]for z in [sl,ti,v]];alpha=sv*pow(vv,-1,p)%p
r=(vv+pow(vv,-1,p))%p
# Rational map formulas, differentiated before finite-field evaluation.
X=v*(k*k-4)/(4*(k-v-1/v));a=(k-2/v)/(k-v-1/v)**2

def det(A):
 return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])-A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])+A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]))%p

def reduce(Pc,A,B):
 p0,p1,p2=Pc;D=(4*A**3+27*B*B)%p
 return [((2*A*A*p1-3*A*B*p2+9*B*p0)*pow(D,-1,p))%p,((-2*A*A*p2+6*A*p0-9*B*p1)*pow(D,-1,p))%p]

records=[];solution=None
for kv in range(0,30):
 try:
  pt=point|{k:kv};Ab=G['scaled']['A'];Bb=G['scaled']['B']
  A=mod(Ab.subs(pt));B=mod(Bb.subs(pt));Av=[mod(sp.diff(Ab,z).subs(pt))for z in [q,h,k]]
  Xv=mod(sp.diff(X,v).subs(pt));Xk=mod(sp.diff(X,k).subs(pt));am=mod(a.subs(pt));av=mod(sp.diff(a,v).subs(pt))*pow(am,-1,p)%p;ak=mod(sp.diff(a,k).subs(pt))*pow(am,-1,p)%p
  dX=[Xv*dpar[q][2]%p,Xv*dpar[h][2]%p,Xk]
  dL=[(dpar[q][0]*kv+dpar[q][1])%p,(dpar[h][0]*kv+dpar[h][1])%p,sv]
  dalpha=[(dpar[z][0]*vv-sv*dpar[z][2])*pow(vv*vv%p,-1,p)%p for z in [q,h]]
  dlogH=[(2*av*dpar[z][2]-3*dalpha[i]*pow(alpha,-1,p))%p for i,z in enumerate([q,h])]+[(2*kv*pow(kv*kv-4,-1,p)+2*ak)%p]
  M=[];line=sv*kv+tv
  for theta in [[1,0,0],[0,1,0]]:
   DL=det([theta,dL,dX]);DA=det([theta,Av,dX]);DH=det([theta,dlogH,dX]);C=4*alpha*alpha*pow(am,-1,p)%p
   Pc=[C*(3*line*DL+DA+(line*line+A)*DH)%p,C*(3*DL+line*DH)%p,C*DH%p]
   M.append(reduce(Pc,A,B))
  M=sp.Matrix([[M[j][i]for j in range(2)]for i in range(2)])
  Al=mod(G['scaled']['A_lambda'].subs(pt));Bl=mod(G['scaled']['B_lambda'].subs(pt));rhs=reduce([Bl*pow(2,-1,p)%p,Al*pow(2,-1,p)%p,0],A,B)
  if solution is None and int(M.det())%p:
   solution=[int(x)%p for x in M.inv_mod(p)*sp.Matrix(rhs)]
  residual=None if solution is None else [(int(x)-rhs[i])%p for i,x in enumerate(M*sp.Matrix(solution))]
  records.append(dict(k=kv,matrix=[[int(M[i,j])for j in range(2)]for i in range(2)],rhs=rhs,theta=solution,residual=residual))
 except (ZeroDivisionError,ValueError):continue
ans=dict(prime=p,point={str(z):v for z,v in point.items()},parameter_derivatives={str(z):v for z,v in dpar.items()},theta_from_first_invertible_k=solution,records=records,all_pointwise_matches=all(r['residual']==[0,0]for r in records if r['residual']is not None),caveat='This checks a sufficient equality of GM representatives without adding a further exact base current. The Gysin formula assumes beta=sqrt(s/v)*theta closed on the intrinsic twist surface.')
(root/'gysin_probe_j0.json').write_text(json.dumps(ans,indent=2));print('theta',solution,'records',len(records),'matches',sum(r['residual']==[0,0]for r in records));print(json.dumps(records[:4],indent=2))
