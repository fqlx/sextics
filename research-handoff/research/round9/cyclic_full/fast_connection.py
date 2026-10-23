"""Exact GM matrices via polynomial coefficient vectors and common denominators.

Avoids expanding rational primitives in the fiber variables.  All source
decompositions are checked as polynomial coefficient-vector identities.
"""
from pathlib import Path
import argparse,sympy as S,json,pickle,time,resource
from sympy.polys.matrices import DomainMatrix
ap=argparse.ArgumentParser();ap.add_argument('--character',type=int,choices=(0,1),default=0);args=ap.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(115,120))
HERE=Path(__file__).resolve().parent;st=time.monotonic();ch=args.character;tag='actual'if ch==0 else'conjugate'
W,h,t,L,r,x=S.symbols('W h t L r x');vv=(W,h,t);bb=(L,r,x);c=S.Rational(5,7)
C=W**6+c*(h**3+t*h)*W**3+L*h**6+r*t*h**4+t**3/x
flow=[x*(L*(c*c-10*r)+4*r*r),-18*L+r*x*(c*c-5*r)+9*r,-x*(x*(c*c+5*r)+27)]
hol=[h*h,t]if ch==0 else[W*h]
def exps(wt,char):return[(a,b,j)for a in range(wt+1)for b in range(wt+1)for j in range(wt//2+1)if a+b+2*j==wt and a%3==char]
def mon(e):return W**e[0]*h**e[1]*t**e[2]
def col(P,rr):
    dd=S.Poly(S.expand(P),vv).as_dict();return S.Matrix([dd.get(e,0)for e in rr])
def labs(degrees):return[(i,e)for i,d in enumerate(degrees)for e in exps(d,(ch+1)%3 if i==0 else ch)]
def jmatrix(rr,lab):return S.Matrix.hstack(*[col(S.diff(C,vv[i])*mon(e),rr)for i,e in lab])
def inv(A):
    d=DomainMatrix.from_Matrix(A);iv,de=d.inv_den();return iv.to_Matrix(),d.domain.to_sympy(de)
def check(A,raw,den,target):assert all(S.expand(z)==0 for z in A*raw-den*target)
rr8=exps(8,ch);lab8=labs((3,3,4));J8=jmatrix(rr8,lab8)
piv=list(J8.row_join(S.eye(len(rr8))).subs({L:2,r:3,x:5}).rref()[1]);assert piv[:len(lab8)]==list(range(len(lab8)))
eta=[mon(rr8[k-len(lab8)])for k in piv if k>=len(lab8)]
A8=(x*J8.row_join(S.Matrix.hstack(*[col(e,rr8)for e in eta]))).applyfunc(S.expand);iv8,de8=inv(A8)
rr14=exps(14,ch);lab14=labs((9,9,10));A14=(x*jmatrix(rr14,lab14)).applyfunc(S.expand)
piv14=list(A14.subs({L:2,r:3,x:5}).rref()[1]);assert len(piv14)==len(rr14)
A14=A14[:,piv14];iv14,de14=inv(A14);lab14sel=[lab14[k]for k in piv14]
print('INVERSES',tag,len(rr8),len(rr14),eta,time.monotonic()-st,flush=True)
def divvec(raw,lab,rr):
    lookup={e:j for j,e in enumerate(rr)};out=S.zeros(len(rr),1)
    for q,(i,e)in zip(raw,lab):
        if e[i]:ee=list(e);ee[i]-=1;out[lookup[tuple(ee)]]+=e[i]*q
    return out.applyfunc(S.expand)
holrows=[S.Poly(z,vv).monoms()[0]for z in hol]
def lower_vector(P):
    target=x*P;raw=iv8*target;check(A8,raw,de8,target)
    dd=divvec(raw[:len(lab8),:],lab8,holrows)
    coeff=dd.col_join(raw[len(lab8):,:])
    return raw,coeff,de8
def lower_poly(P):return lower_vector(col(P,rr8))
source=None
if ch==0:
    raw,coef,den=lower_poly(h**4*t*t);source={'coefficients':[S.cancel(z/den)for z in coef],'Q8_raw':raw[:len(lab8),:],'Q8_denominator':den}
matrices={};primitives={}
for z,DC,scale in zip(bb,(h**6,t*h**4,-t**3),(1,1,1/x**2)):
    rows=[];pp=[]
    for hh in hol:
        raw,coef,den=lower_poly(hh*DC)
        rows.append([S.cancel(-scale*q/den)for q in coef]);pp.append({'Q8_raw':raw[:len(lab8),:],'Q8_denominator':den/scale,'Q14_raw':None})
    for ee in eta:
        target=x*col(ee*DC,rr14);raw14=iv14*target;check(A14,raw14,de14,target)
        P8=divvec(raw14,lab14sel,rr8)
        raw8,coef,den8=lower_vector(P8);den=den8*de14
        rows.append([S.cancel(-scale*q/den)for q in coef]);pp.append({'Q8_raw':raw8[:len(lab8),:],'Q8_denominator':den/scale,'Q14_raw':raw14,'Q14_denominator':de14/scale})
    matrices[str(z)]=S.Matrix(rows);primitives[str(z)]=pp
    payload={'symbols':(W,h,t,L,r,x),'curve':C,'hol':hol,'eta':eta,'basis':hol+eta,'basis_pole_orders':[1]*len(hol)+[2]*len(eta),'connection':matrices,'primitives':primitives,'lab8':lab8,'lab14':lab14sel,'source_h4t2':source,'connection_convention':'d_z beta_i=sum_j N_z[i,j]beta_j+fiber exact correction','seconds':time.monotonic()-st}
    (HERE/(tag+'_fast.pickle')).write_bytes(pickle.dumps(payload));print('EXPORTED',tag,z,time.monotonic()-st,flush=True)
Nflow=sum((v*matrices[str(z)]for z,v in zip(bb,flow)),S.zeros(3))
if ch==0:
    expected=S.Matrix([[(-2*c*c*x+10*r*x-27)/3,3],[-3*r*x,-(2*c*c*x+5*r*x+54)/3]])
    assert all(S.cancel(z)==0 for z in Nflow[:2,:2]-expected)
    assert all(S.cancel(z)==0 for z in Nflow[:2,2])
    assert all(S.cancel(z)==0 for z in S.Matrix(source['coefficients'])+matrices['r'][1,:].T)
else:
    ref=json.load(open('/workspace/research/round8/cyclic_companion/gist/conjugate_reference.json'))
    assert all(S.cancel(z)==0 for z in Nflow-S.Matrix([[S.sympify(q)for q in row]for row in ref['generic_connection']]))
print('SOURCE_AND_FLOW_MATCH',tag,time.monotonic()-st,flush=True)
curvature={}
for i in range(3):
    for j in range(i+1,3):
        Ni,Nj=matrices[str(bb[i])],matrices[str(bb[j])]
        F=Nj.diff(bb[i])-Ni.diff(bb[j])+Nj*Ni-Ni*Nj
        assert all(S.cancel(z)==0 for z in F)
        curvature[str((bb[i],bb[j]))]=True;print('FLAT',tag,bb[i],bb[j],time.monotonic()-st,flush=True)
out={'scope':'Exact full transverse GM and fiber correction data; no primitive or certificate.','tag':tag,'basis':list(map(str,hol+eta)),'connection':{z:[[str(q)for q in row]for row in N.tolist()]for z,N in matrices.items()},'flatness':curvature,'nullflow_match':True,'seconds':time.monotonic()-st}
if source:out['source_h4t2_coefficients']=list(map(str,source['coefficients']))
(HERE/(tag+'_fast.json')).write_text(json.dumps(out,indent=2)+'\n');print('DONE',tag,time.monotonic()-st,flush=True)
