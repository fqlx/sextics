#!/usr/bin/env python3
"""Independent affine sign/primitive audit for marked-point Abel--Prym forms.

For R=P*C_j=sum_i Qi*Ci+eta, U=QW-W*Qh. On h=1,
div_aff(U,Qt-2tQh)+6Qh=div_weighted(Q). Thus direct differentiation
of P*dW/Ct on C=0 gives d_j beta-N_j beta=d_curve(U/Ct), with PLUS
primitive U/Ct. The sampled audit computes both sides afresh on the curve.
"""
import pickle,json,random,time
from pathlib import Path
import sympy as s
from search import Poly,qmod,HERE

start=time.time();p=1000003;rng=random.Random(9981);c=qmod('5/7',p)
def comp(f,vars):
    n,d=s.fraction(f);return Poly(s.Poly(n,*vars).as_dict(),p),Poly(s.Poly(d,*vars).as_dict(),p)
def ev(pair,point):return pair[0].eval(point)*pow(pair[1].eval(point),-1,p)%p

blocks=[]
for name,nhol in [('actual',2),('conjugate',1)]:
    d=pickle.load(open(HERE.parent/f'cyclic_full/{name}_fast.pickle','rb'));vars=d['symbols'][3:]
    basis=[]
    for numerator,order in zip(d['basis'],d['basis_pole_orders']):
        W,h,t=d['symbols'][:3];f=s.Poly(numerator.subs(h,1),W,t).as_dict();basis.append((f,order))
    directions={}
    for j in ('L','r','x'):
        entries=[]
        for i in range(nhol):
            pp=d['primitives'][j][i]
            entries.append({'N':[comp(t,vars) for t in d['connection'][j][i,:]],'raw':[comp(t,vars) for t in pp['Q8_raw']],'den':comp(pp['Q8_denominator'],vars)})
        directions[j]=entries
    blocks.append((name,d['lab8'],basis,directions))

def fib(poly,W,t,der=None):
    out=0
    for (a,b),coef in poly.items():
        a,b=int(a),int(b);coef=qmod(coef,p)
        if der=='W':coef*=a;a-=1
        if der=='t':coef*=b;b-=1
        if a>=0 and b>=0:out+=coef*pow(W,a,p)*pow(t,b,p)
    return out%p

checks=0;records=[]
while len(records)<12:
    w,tt,rr,xx=[rng.randrange(1,p) for _ in range(4)]
    ll=(-pow(w,6,p)-c*(1+tt)*pow(w,3,p)-rr*tt-pow(tt,3,p)*pow(xx,-1,p))%p
    par=(ll,rr,xx);Ct=(c*pow(w,3,p)+rr+3*tt*tt*pow(xx,-1,p))%p
    if not Ct:continue
    Ctt=6*tt*pow(xx,-1,p)%p;CtW=3*c*w*w%p;CW=(6*pow(w,5,p)+3*c*(1+tt)*w*w)%p
    try:
        for name,labels,basis,directions in blocks:
            bvals=[]
            for f,order in basis:
                val=fib(f,w,tt)
                bvals.append(val*pow(Ct,-1,p)%p if order==1 else (fib(f,w,tt,'t')*pow(Ct,-2,p)-val*Ctt*pow(Ct,-3,p))%p)
            for j,entries in directions.items():
                Cz={'L':1,'r':tt,'x':-pow(tt,3,p)*pow(xx,-2,p)}[j]%p
                Czt={'L':0,'r':1,'x':-3*tt*tt*pow(xx,-2,p)}[j]%p
                for i,e in enumerate(entries):
                    P=fib(basis[i][0],w,tt);Pt=fib(basis[i][0],w,tt,'t');R=P*Cz%p;Rt=(Pt*Cz+P*Czt)%p
                    deriv=(-Rt*pow(Ct,-2,p)+R*Ctt*pow(Ct,-3,p))%p
                    N=[ev(z,par) for z in e['N']];connection=sum(v*z for v,z in zip(N,bvals))%p
                    den=ev(e['den'],par);Q=[0,0,0];QW=[0,0,0];Qt=[0,0,0]
                    for pair,(compidx,(a,b,k)) in zip(e['raw'],labels):
                        coef=ev(pair,par)*pow(den,-1,p)%p
                        Q[compidx]+=coef*pow(w,a,p)*pow(tt,k,p)
                        if a:QW[compidx]+=coef*a*pow(w,a-1,p)*pow(tt,k,p)
                        if k:Qt[compidx]+=coef*k*pow(w,a,p)*pow(tt,k-1,p)
                    U=(Q[0]-w*Q[1])%p;Uw=(QW[0]-Q[1]-w*QW[1])%p;Ut=(Qt[0]-w*Qt[1])%p
                    Fprime=(Uw*pow(Ct,-1,p)-U*CtW*pow(Ct,-2,p)-Ut*CW*pow(Ct,-2,p)+U*CW*Ctt*pow(Ct,-3,p))%p
                    assert (deriv-connection-Fprime)%p==0,(name,j,i,par)
                    checks+=1
    except (ZeroDivisionError,ValueError):continue
    records.append({'W':w,'t':tt,'Lrx':par})
out={'prime':p,'points':records,'checks':checks,'all_direct_primitive_derivatives_match':True,'sign':'PLUS F=(Q8_W-W*Q8_h)/C_t','universal_identity':'div_aff(QW-WQh,Qt-2tQh)+6Qh=div_weighted Q for Qh weighteddegree3','scope':'Independent finite-prime replay of absolute lift; universal derivation plus exact stored Griffiths identities gives characteristic-zero sign. No source moment or certificate claim.','seconds':time.time()-start}
(HERE/'absolute_lift_audit.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
