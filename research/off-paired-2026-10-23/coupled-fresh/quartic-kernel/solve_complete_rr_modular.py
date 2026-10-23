#!/usr/bin/env python3
"""Attempt the actual source preimage in its complete RR space over GF(p).

This is a complete relative w problem, not a certificate degree search.
The source and all 274 Riemann--Roch columns are retained.
"""
import json,time
from pathlib import Path
import numpy as np
import sympy as s
from actual_h_modular import ActualH

HERE=Path(__file__).resolve().parent
P=1009;I=2;J=1;ELL=3
w,z=s.symbols('w z')
inv=lambda x:pow(int(x)%P,-1,P)
pol=lambda x:s.Poly(x,w,modulus=P)
T=pol(1+w**3)
N=pol(9*w*w-16*s.Rational(J,I*I)*T.as_expr())
L=pol(256*T.as_expr()**5*N.as_expr()+729*I**6*s.Rational(J,I*I)*w**6)
C=-(L.diff()*pol(w)*N*T-L*(N*T+pol(w)*N.diff()*T+2*pol(w)*N*T.diff()))
assert C.degree()==24
Cp=C.diff();Lp=L.diff();Tp=T.diff()
ev=lambda a,x:int(a.eval(x))%P
uu=s.symbols('u')
pv=J*ELL; qv=I*ELL*ELL+ELL+1
bounds=[72,74,61,63]
cols=[(j,k)for j,b in enumerate(bounds)for k in range(b+1)]
assert len(cols)==274

def field_connection(f,fp):
    r=f*pow(ELL,6,P)%P;rp=fp*pow(ELL,6,P)%P
    F=s.Poly(r*uu**4+qv*uu**2+pv*uu+1,uu,modulus=P)
    ip=s.invert(F.diff(),F)
    du=(-s.Poly(rp*uu**4,uu,modulus=P)*ip).rem(F)
    gamma=[]
    for j in range(4):
        pp=s.Poly(0,uu,modulus=P)if not j else(s.Poly(j*uu**(j-1),uu,modulus=P)*du).rem(F)
        gamma.append(np.array([int(pp.nth(k))%P for k in range(4)],dtype=np.int64))
    return np.stack(gamma,axis=1),np.array([int(du.nth(k))%P for k in range(4)],dtype=np.int64)

def rows_at(x,h):
    cv=ev(C,x);tv=ev(T,x);lv=ev(L,x)
    if not(cv and tv and lv):raise ZeroDivisionError
    detail=h.point(x,True)
    gamma,du=field_connection(detail['f'],detail['f_w'])
    base=[inv(cv)**3%P,inv(cv)**3%P,lv*inv(tv)*inv(cv)**3%P,lv*inv(tv)*inv(cv)**3%P]
    logarithm=[-3*ev(Cp,x)*inv(cv)%P]*2
    logarithm+= [(ev(Lp,x)*inv(lv)-ev(Tp,x)*inv(tv)-3*ev(Cp,x)*inv(cv))%P]*2
    out=np.zeros((4,275),dtype=np.int64)
    for col,(j,k)in enumerate(cols):
        vv=base[j]*pow(x,k,P)%P
        derivative=vv*(logarithm[j]+k*inv(x))%P
        out[:,col]=vv*gamma[:,j]%P
        out[j,col]=(out[j,col]+derivative)%P
    out[:,-1]=(-ELL*ELL*detail['H']*inv(6)*du)%P
    return out

def run():
    started=time.monotonic();h=ActualH(P,I,J,order=3)
    pivots={};points=[];inconsistent=None
    for x in range(1,P):
        try:mat=rows_at(x,h)
        except(AssertionError,ZeroDivisionError,s.polys.polyerrors.NotInvertible):continue
        points.append(x)
        for raw in mat:
            row=raw.copy()
            for col,pr in sorted(pivots.items()):
                if row[col]:row=(row-row[col]*pr)%P
            nz=np.flatnonzero(row)
            if not len(nz):continue
            col=int(nz[0]);row=row*inv(row[col])%P
            pivots[col]=row
            if col==274:
                inconsistent={'w':x,'coefficient_rank':len(pivots)-1,'augmented_rank':len(pivots)}
                break
        if inconsistent:break
        if len(points)>=95:break
    coeff_rank=sum(k<274 for k in pivots)
    out={'source_sha256':h.source_sha,'arithmetic':'exact GF(1009), all full-coordinate jets before specialization',
         'point':{'i':I,'J':J,'j':1,'l':ELL},'columns':274,'complete_space':'COMPLETE-W-PRIMITIVE-SPACE.md',
         'source_normalization':'originalH+LEQF+LDQG+L3(QHminus+QHplus)-LDQDinf; constant retained',
         'points':points,'rows':4*len(points),'coefficient_rank':coeff_rank,'augmented_rank':len(pivots),
         'inconsistent':inconsistent is not None,
         'scope':'This is the complete relative w source-preimage problem at one good specialization. It is not a global sextic certificate obstruction; i,j currents and source-lift changes remain available.',
         'elapsed_seconds':time.monotonic()-started}
    if not inconsistent:
        sol=np.zeros(274,dtype=np.int64)
        for col,row in sorted(pivots.items(),reverse=True):
            if col<274:sol[col]=(row[-1]-np.dot(row[col+1:274],sol[col+1:]))%P
        out['candidate_coefficients']=[int(x)for x in sol]
        out['candidate_status']='Needs full exact field identity verification and characteristic-zero reconstruction'
    else:
        out['relative_feedback']='The actual normalized source needs i/j currents or further source-lift changes; do not promote this to sextic nonexistence.'
    path=HERE/'complete-rr-modular-source-results.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in ['candidate_coefficients','points']},indent=2))

if __name__=='__main__':run()
