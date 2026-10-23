"""Exact arbitrary-exponent audit of the rational coupled Theta operators.

The normalized operators act on c^alpha*d^(2 beta)*e^n.  The proposed
rational operators act independently on i^alpha*J^beta*v^gamma, with the
complete e weight restored.  Equality for formal exponents establishes
equality of these rational differential operators in characteristic zero.
"""
import json
from collections import defaultdict
from pathlib import Path
import sympy as s

aa,bb,mm=s.symbols('alpha beta gamma')
R=s.Rational

def clean(F):return {k:s.factor(v) for k,v in F.items() if s.factor(v)!=0}
def add(*Fs):
    out=defaultdict(lambda:0)
    for F in Fs:
        for k,v in F.items():out[k]+=v
    return clean(out)
def scale(k,F):return clean({x:k*y for x,y in F.items()})
def seq(F,*ops):
    for op in ops:F=op(F)
    return F

def normalized(ell):
    nn=ell-2*aa-2*bb+6*mm
    def deriv(j):
        def op(F):
            out=defaultdict(lambda:0)
            for sh,co in F.items():
                xs=(aa+sh[0],2*bb+sh[1],nn+sh[2])
                out[tuple(k-(t==j) for t,k in enumerate(sh))]+=co*xs[j]
            return clean(out)
        return op
    def eu(kind,constant=0):
        def op(F):
            out={}
            for sh,co in F.items():
                x,y,z=aa+sh[0],2*bb+sh[1],nn+sh[2]
                ev={'A':-x/3-2*y/3-z/6,
                    'B':-x/3-y/6-z/6,
                    'T':-x/3-y/6-2*z/3}[kind]
                out[sh]=co*(ev+constant)
            return clean(out)
        return op
    return deriv(0),deriv(1),deriv(2),eu

def inv_deriv(j):
    def op(F):
        out=defaultdict(lambda:0)
        for sh,co in F.items():
            ex=(aa+sh[0],bb+sh[1],mm+sh[2])
            out[tuple(k-(t==j)for t,k in enumerate(sh))]+=co*ex[j]
        return clean(out)
    return op
A=inv_deriv(0);B=inv_deriv(1)
def eu_inv(x,y,z,constant=0):
    return lambda F:clean({sh:co*(x*(aa+sh[0])+y*(bb+sh[1])+z*(mm+sh[2])+constant) for sh,co in F.items()})
Z=eu_inv(0,0,1)
def D(k=0):return eu_inv(-2,-2,6,k)
def ZJB(k=0):return eu_inv(0,1,1,k)
def ZDhalf(k=0):return eu_inv(-1,-1,4,k)
def mult_shift(di=0,dj=0,dv=0):
    return lambda F:clean({(sh[0]+di,sh[1]+dj,sh[2]+dv):co for sh,co in F.items()})
J=mult_shift(dj=1);V=mult_shift(dv=1);Vinv=mult_shift(dv=-1)
one={(0,0,0):s.Integer(1)}

def to_normalized(F,ellin,ellout):
    return clean({(di,2*dj,ellout-ellin-2*di-2*dj+6*dv):co for (di,dj,dv),co in F.items()})
checks={}
def check(name,actual,pred,ellin,ellout):
    expected=to_normalized(pred,ellin,ellout)
    checks[name]=not add(actual,scale(-1,expected))
    assert checks[name],(name,actual,expected)

# Four cross rows, compared in both the zeta and raw-xi coefficients.
for j,ell in enumerate((-3,-4,-6,-7),1):
    C,dd,E,eu=normalized(ell)
    if j==1:
        nz=seq(one,C,C)
        nx=seq(one,eu('B',-R(1,2)),E)
        rz=seq(one,A,A)
        rx=scale(-1,seq(one,Z,D(-3)))
    elif j==2:
        nz=seq(one,E,C)
        nx=seq(one,eu('B',-R(2,3)),eu('T',-R(5,3)))
        rz=seq(one,D(-4),A)
        rx=seq(one,Z,ZDhalf(-1))
    elif j==3:
        nz=seq(one,eu('A',-1),E)
        nx=seq(one,C,C)
        rz=scale(-1,seq(one,ZJB(),D(-6)))
        rx=seq(one,A,A,Vinv)
    else:
        nz=seq(one,eu('A',-R(7,6)),eu('T',-R(5,3)))
        nx=seq(one,E,C)
        rz=seq(one,ZJB(),ZDhalf(-3))
        rx=seq(one,D(-7),A,Vinv)
    check(f'cross_{j}_zeta',nz,rz,ell,-7)
    check(f'cross_{j}_xi',nx,rx,ell,-4)

def self_rows(prefix,ells,shifts,output):
    for j,ell in enumerate(ells,1):
        C,dd,E,eu=normalized(ell)
        if j==1:
            actual=add(seq(one,E,E),scale(-1,seq(one,eu('T',-R(4,3)),C)))
            if prefix=='zeta':pred=add(seq(one,D(-5),D(-6)),seq(one,ZDhalf(-2),A))
            else:pred=add(seq(one,D(-2),D(-3)),seq(one,ZDhalf(),A))
        elif j==2:
            actual=add(seq(one,dd,dd),scale(-1,seq(one,eu('A',shifts[0]),C)))
            pred=add(scale(4,seq(one,B,B,J)),scale(2,seq(one,B)),seq(one,ZJB(),A))
        else:
            actual=add(seq(one,C,C,C),scale(-1,seq(one,eu('T',-R(5,3)),eu('B',shifts[1]),eu('A',shifts[2]))))
            if prefix=='zeta':cubic=seq(one,ZDhalf(1),Z,ZJB(1),V)
            else:cubic=seq(one,ZDhalf(3),eu_inv(0,0,1,1),ZJB(1),V)
            pred=add(seq(one,A,A,A),cubic)
        check(f'{prefix}_self_{j}',actual,pred,ell,output)

self_rows('zeta',(-5,-5,-1),(-R(5,6),-R(1,6),-R(7,6)),-7)
self_rows('xi',(-2,-2,2),(-R(1,3),-R(2,3),-R(2,3)),-4)

out={'passed':True,'checks':checks,'certificate':False,
     'scope':'Formal arbitrary-exponent equality of all14 rational self/cross operators; no candidate potentials or compact closure asserted.'}
Path(__file__).with_name('rational-coupled-theta-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact arbitrary-exponent operator identities')
