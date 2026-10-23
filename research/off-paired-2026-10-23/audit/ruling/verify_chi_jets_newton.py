#!/usr/bin/env python3
"""Independent finite Taylor-root check of all 19 saved physical chi jets.

No primary module or derivative formula is imported. Solve the actual
quartic root by Taylor Newton iteration over F_1009, differentiate the
saved RR primitives directly along the curve, and compare literal forms
at independent affine points. This is a local data audit, not an exact
characteristic-zero primitive or a replacement for global ideal checks.
"""
from fractions import Fraction
from pathlib import Path
from math import factorial
import hashlib,json

HERE=Path(__file__).resolve().parent
P=1009;ZERO=(0,0,0);ORDER=3


def fp(v):
    if isinstance(v,Fraction):return v.numerator*pow(v.denominator,-1,P)%P
    return int(v)%P


class Taylor:
    def __init__(self,c=0):self.c=({e:fp(v) for e,v in c.items() if fp(v)} if isinstance(c,dict) else ({ZERO:fp(c)} if fp(c) else {}))
    @property
    def value(self):return self.c.get(ZERO,0)
    def __add__(self,y):
        y=cast(y);out=dict(self.c)
        for e,v in y.c.items():out[e]=(out.get(e,0)+v)%P
        return Taylor(out)
    __radd__=__add__
    def __neg__(self):return Taylor({e:-v for e,v in self.c.items()})
    def __sub__(self,y):return self+-cast(y)
    def __rsub__(self,y):return cast(y)+-self
    def __mul__(self,y):
        y=cast(y);out={}
        for e,v in self.c.items():
            for f,w in y.c.items():
                g=tuple(x+y for x,y in zip(e,f))
                if sum(g)<=ORDER:out[g]=(out.get(g,0)+v*w)%P
        return Taylor(out)
    __rmul__=__mul__
    def inverse(self):
        a=pow(self.value,-1,P);n=self*a-1;out=Taylor(1);term=Taylor(1)
        for _ in range(ORDER):term=-term*n;out=out+term
        return a*out
    def __truediv__(self,y):return self*cast(y).inverse()
    def __rtruediv__(self,y):return cast(y)*self.inverse()
    def __pow__(self,n):
        if n<0:return self.inverse()**(-n)
        out=Taylor(1);x=self
        while n:
            if n&1:out=out*x
            n//=2
            if n:x=x*x
        return out


def cast(y):return y if isinstance(y,Taylor) else Taylor(y)
def var(i):
    e=[0,0,0];e[i]=1
    return Taylor({ZERO:1,tuple(e):1})
def unitpower(u,a):
    assert u.value==1
    out=Taylor(1);term=Taylor(1);c=Fraction(1)
    for j in range(1,ORDER+1):
        term=term*(u-1);c*=Fraction(a-j+1,j);out=out+fp(c)*term
    return out
def inv(n):return pow(n%P,-1,P)


def monvalue(e,point,deriv=None):
    ee=list(e);coef=1
    if deriv is not None:
        coef=ee[deriv]
        if not coef:return 0
        ee[deriv]-=1
    for v,n in zip(point,ee):coef=coef*pow(v,n,P)%P
    return coef


def dot(x,y):return sum(a*b for a,b in zip(x,y))%P


def rref(a):
    a=[row[:] for row in a];row=0;piv=[]
    for c in range(len(a[0])):
        k=next((j for j in range(row,len(a)) if a[j][c]),None)
        if k is None:continue
        a[row],a[k]=a[k],a[row];v=inv(a[row][c]);a[row]=[x*v%P for x in a[row]]
        for j in range(row+1,len(a)):
            v=a[j][c];a[j]=[(x-v*y)%P for x,y in zip(a[j],a[row])]
        piv.append(c);row+=1
        if row==len(a):break
    return piv


def main():
    folder=HERE.parents[1]/'coupled-fresh/genus4-gm-independent'
    paths=[folder/'rr-basis-results.json',folder/'chi-physical-third-jets-results.json']
    rr,data=[json.loads(p.read_text()) for p in paths]
    assert rr['prime']==data['prime']==P
    target=dict(A=2,B=2,C=inv(3),D=inv(2),E=inv(2),T=2)
    assert data['specialization']==rr['specialization']==target
    labels=data['derivative_labels'];assert len(labels)==19
    A,B,C,D,E,T=[target[k] for k in 'ABCDET']
    compactmatrix=[list(row) for row in zip(*data['compact_columns'])]
    piv=rref(compactmatrix)
    assert len(piv)==8 and piv==data['compact_pivot_derivative_indices']
    Rj,Sj,zj=[var(i) for i in range(3)]
    kj=unitpower(Rj,Fraction(1,6))*unitpower(Sj,Fraction(1,6))
    Aj=1+Rj;Bj=1+Sj;Cj=kj/3;Dj=zj*kj/2;Ej=zj/2;Tj=1+zj**6
    assert not (kj**6-Rj*Sj).c
    normalizer=unitpower(Tj/Bj,Fraction(-1,2))
    points=[];check_count=0
    # Choose roots afresh from the actual affine curve. These are not
    # the marked local branches used in the primary RR construction.
    for q in range(1,100):
        perq=0
        for a in range(1,P):
            b=pow(q,3,P)*inv(a)%P
            if (A*a*a+B*b*b+C*q*q+D*a*q+E*q+T)%P:continue
            J=(2*A*a*a+D*a*q-2*B*b*b)%P
            if not J:continue
            bj=Taylor(b)
            for _ in range(3):
                pol=Bj*bj**4+(Cj*q*q+Ej*q+Tj)*bj**2+Dj*q**4*bj+Aj*q**6
                dp=4*Bj*bj**3+2*(Cj*q*q+Ej*q+Tj)*bj+Dj*q**4
                bj=bj-pol/dp
            assert bj.value==b
            assert not (Bj*bj**4+(Cj*q*q+Ej*q+Tj)*bj**2+Dj*q**4*bj+Aj*q**6).c
            aj=q**3/bj
            assert not (Aj*aj**2+Bj*bj**2+Cj*q*q+Dj*aj*q+Ej*q+Tj).c
            literal=(bj/q)*normalizer
            Qa=(2*A*a+D*q)%P;Qb=2*B*b%P;Qq=(2*C*q+D*a+E)%P
            aq=(-a*Qq-3*q*q*Qb)*inv(J)%P
            bq=(b*Qq+3*q*q*Qa)*inv(J)%P
            Jq=(D*a+(4*A*a+D*q)*aq-4*B*b*bq)%P
            point=(a,b,q,1)
            values=[monvalue(e,point) for e in rr['quotient_monomials']]
            compact=[dot(row,values)*inv(pow(q,5,P)*J)%P for row in rr['RR_kernel_rows']]
            mons=data['exact_function_monomials']
            hv=[monvalue(e,point) for e in mons]
            hq=[(monvalue(e,point,2)+aq*monvalue(e,point,0)+bq*monvalue(e,point,1))%P for e in mons]
            exact=[]
            den=pow(J,3,P)*pow(q,4,P)%P
            for row in data['exact_function_numerator_rows']:
                h=dot(row,hv);dh=dot(row,hq)
                exact.append((dh-h*(3*Jq*inv(J)+4*inv(q)))*inv(den)%P)
            for j,label in enumerate(labels):
                multi=tuple(label.count(c) for c in ('R','S','z'))
                factor=1
                for n in multi:factor*=factorial(n)
                expected=literal.c.get(multi,0)*factor%P
                represented=(dot(data['compact_columns'][j],compact)+dot(data['exact_function_coefficients'][j],exact))%P
                assert represented==expected,(point,label,represented,expected)
                check_count+=1
            points.append({'a':a,'b':b,'q':q,'J':J});perq+=1
            if perq==2:break
        if len(points)>=12:break
    assert len(points)>=12
    out={'status':'passed','prime':P,'physical_point':data['physical_point'],
        'curve_points':points,'literal_jet_checks':check_count,'derivative_labels':labels,
        'compact_rank':len(piv),'pivot_derivative_indices':piv,'pivot_derivative_labels':[labels[i] for i in piv],
        'method':'Independent truncated Taylor Newton roots of the actual physical quartic and b0 normalization; saved compact and exact representatives evaluated with direct curve q derivative. No primary code or derivative formula imported.',
        'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope':'Checks all19 derivative identities at12 independent affine curve points over1009 and recomputes compact rank8. Does not reprove global RR completeness or exact ideal identities, and gives no primitive/source solution.'}
    (HERE/'chi-jets-newton-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
