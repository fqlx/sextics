"""Actual ζ Prym block: holomorphic basis h²,t, one pole-two class."""
from pathlib import Path
import sympy as S,json,pickle,time,resource
from sympy.polys.matrices import DomainMatrix
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(175,180))
HERE=Path(__file__).resolve().parent;st=time.monotonic()
W,h,t,L,r,x=S.symbols('W h t L r x');c=S.Rational(5,7);variables=(W,h,t);base=(L,r,x)
C=W**6+c*(h**3+t*h)*W**3+L*h**6+r*t*h**4+t**3/x
flow=[x*(L*(c*c-10*r)+4*r*r),-18*L+r*x*(c*c-5*r)+9*r,-x*(x*(c*c+5*r)+27)]
def mons(wt,ch):return [W**a*h**b*t**j for a in range(wt+1)for b in range(wt+1)for j in range(wt//2+1)if a+b+2*j==wt and a%3==ch]
def rows(wt,ch):return [(a,b,j)for a in range(wt+1)for b in range(wt+1)for j in range(wt//2+1)if a+b+2*j==wt and a%3==ch]
def col(pol,rr):
    pp=S.Poly(S.expand(pol),*variables)
    return S.Matrix([pp.coeff_monomial(W**a*h**b*t**j)for a,b,j in rr])
def canon(q):return S.factor(S.cancel(q))
def inverse_den(A):
    DM=DomainMatrix.from_Matrix(A);iv,de=DM.inv_den()
    return iv.to_Matrix(),DM.domain.to_sympy(de)
r8=rows(8,0);lab8=[(v,m)for v,wt,ch in [(W,3,1),(h,3,0),(t,4,0)]for m in mons(wt,ch)]
J8=S.Matrix.hstack(*[col(S.diff(C,v)*m,r8)for v,m in lab8])
pv=list(J8.row_join(S.eye(len(r8))).subs({L:2,r:3,x:5}).rref()[1]);assert pv[:len(lab8)]==list(range(len(lab8)))
eta_idx=[k-len(lab8)for k in pv if k>=len(lab8)];assert len(eta_idx)==1
eta=[W**r8[k][0]*h**r8[k][1]*t**r8[k][2]for k in eta_idx]
B8=J8.row_join(S.Matrix.hstack(*[col(e,r8)for e in eta]));iv8,de8=inverse_den((x*B8).applyfunc(S.expand))
print('LOWER',len(r8),eta,time.monotonic()-st,flush=True)
r14=rows(14,0);lab14=[(v,m)for v,wt,ch in [(W,9,1),(h,9,0),(t,10,0)]for m in mons(wt,ch)]
J14=S.Matrix.hstack(*[col(S.diff(C,v)*m,r14)for v,m in lab14]);A14=(x*J14).applyfunc(S.expand)
pv14=list(A14.subs({L:2,r:3,x:5}).rref()[1]);assert len(pv14)==len(r14)
iv14,de14=inverse_den(A14[:,pv14]);print('HIGHER',len(r14),time.monotonic()-st,flush=True)
def red8(P):
    tt=x*col(P,r8);qs=(iv8*tt).applyfunc(lambda q:canon(q/de8))
    assert all(S.cancel(z)==0 for z in x*B8*qs-tt)
    pol=[S.factor(sum(qs[k]*m for k,(v,m)in enumerate(lab8)if v==vv))for vv in variables]
    div=S.expand(sum(S.diff(q,v)for q,v in zip(pol,variables)))
    assert S.cancel(P-sum(S.diff(C,v)*q for q,v in zip(pol,variables))-qs[-1]*eta[0])==0
    ph=S.Poly(div,*variables);coeff=[canon(ph.coeff_monomial(z))for z in (h*h,t)]
    assert S.cancel(div-coeff[0]*h*h-coeff[1]*t)==0
    return pol,canon(qs[-1]),coeff
source_Q,source_eta,source_hol=red8(h**4*t*t)
source={'source_numerator':h**4*t*t,'coefficients':source_hol+[source_eta],'Q8':source_Q,'sign':'positive reduction of Res(P Omega/C²)'}
print('SOURCE',source['coefficients'],time.monotonic()-st,flush=True)
matrices={};all_primitives={}
for basevar in base:
    DC=S.diff(C,basevar);conn=[];prims=[]
    for hol in (h*h,t):
        Q8,rr,dd=red8(hol*DC);conn.append([-dd[0],-dd[1],-rr]);prims.append({'Q8':Q8,'Q14':None})
    for e in eta:
        tt=x*col(e*DC,r14);qq=(iv14*tt).applyfunc(lambda q:canon(q/de14))
        assert all(S.cancel(v)==0 for v in A14[:,pv14]*qq-tt)
        Q14=[S.factor(sum(q*m for q,k in zip(qq,pv14)for v,m in [lab14[k]]if v==vv))for vv in variables]
        assert S.cancel(e*DC-sum(S.diff(C,v)*q for q,v in zip(Q14,variables)))==0
        P8=S.expand(sum(S.diff(q,v)for q,v in zip(Q14,variables)))
        Q8,rr,dd=red8(P8);conn.append([-dd[0],-dd[1],-rr]);prims.append({'Q8':Q8,'Q14':Q14})
    matrices[str(basevar)]=S.Matrix(conn);all_primitives[str(basevar)]=prims
    payload={'symbols':(W,h,t,L,r,x),'curve':C,'basis':[h*h,t]+eta,'basis_pole_orders':[1,1,2],'connection_convention':'d_v beta_i=sum_j N_v[i,j]*beta_j+relative exact correction','connection':matrices,'primitives':all_primitives,'source_h4t2':source,'flow':flow,'seconds':time.monotonic()-st}
    (HERE/'actual_connection.pickle').write_bytes(pickle.dumps(payload))
    print('EXPORTED',basevar,time.monotonic()-st,flush=True)
Nflow=sum((v*matrices[str(z)]for z,v in zip(base,flow)),S.zeros(3))
M=S.Matrix([[(-2*c*c*x+10*r*x-27)/3,3],[-3*r*x,-(2*c*c*x+5*r*x+54)/3]])
assert all(canon(z)==0 for z in Nflow[:2,:2]-M)
assert all(canon(z)==0 for z in Nflow[:2,2])
print('NULLFLOW_HOL_MATCH',time.monotonic()-st,flush=True)
curvature={}
for i in range(3):
    for j in range(i+1,3):
        Ni,Nj=matrices[str(base[i])],matrices[str(base[j])]
        F=(Nj.diff(base[i])-Ni.diff(base[j])+Nj*Ni-Ni*Nj).applyfunc(canon);assert F==S.zeros(3)
        curvature[str((base[i],base[j]))]=True;print('FLAT',base[i],base[j],time.monotonic()-st,flush=True)
out={'scope':'Actual ζ Prym full three-direction connection and source class, no primitive or certificate.','basis':['Res(h² Omega/C)','Res(t Omega/C)','Res('+str(eta[0])+' Omega/C²)'],'source_h4t2_coefficients':list(map(str,source['coefficients'])),'connection':{z:[[str(q)for q in row]for row in N.tolist()]for z,N in matrices.items()},'nullflow_hol_match':True,'flatness':curvature,'seconds':time.monotonic()-st}
(HERE/'actual_connection.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',time.monotonic()-st,flush=True)
