"""Test an exact connection-free holomorphic-current potential seed."""
from pathlib import Path
import json,itertools
from flint import fmpq,fmpq_mat
import direct_source as ds

HERE=Path(__file__).parent
ds.exps=[e for n in range(4)for e in itertools.product(range(n+1),repeat=3)if sum(e)==n]
ds.index={e:i for i,e in enumerate(ds.exps)}
ds.products=[(i,j,ds.index[tuple(a+b for a,b in zip(e,f))])for i,e in enumerate(ds.exps)for j,f in enumerate(ds.exps)if sum(e)+sum(f)<=3]
Jet=ds.Jet

def derivative(f,i):
    z=Jet()
    for e,c in zip(ds.exps,f.c):
        if e[i]:
            n=list(e);n[i]-=1;z.c[ds.index[tuple(n)]]+=e[i]*c
    return z

def grad(f):return [derivative(f,i).c[0]for i in range(3)]
def hess(f):return [[derivative(derivative(f,i),j).c[0]for j in range(3)]for i in range(3)]

def point_test(point):
    a,b,v=[Jet(n)for n in point]
    for i,z in enumerate([a,b,v]):
        e=[0]*3;e[i]=1;z.c[ds.index[tuple(e)]]=1
    c=fmpq(5,7);B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
    beta=-R/(3*S);M=1+B*beta
    L=(P+Q*beta+R*beta**2+S*beta**3)/(M*M)
    r=(Q-R*R/(3*S))/(B*M);x=B**3/(S*M)
    jets=[L,r,x]
    J=[[derivative(f,i)for i in range(3)]for f in jets]
    det=J[0][0]*(J[1][1]*J[2][2]-J[1][2]*J[2][1])-J[0][1]*(J[1][0]*J[2][2]-J[1][2]*J[2][0])+J[0][2]*(J[1][0]*J[2][1]-J[1][1]*J[2][0])
    inv=fmpq_mat([[z.c[0]for z in row]for row in J]).inv()
    eps=M/M.c[0]-1
    rho=1+eps/3-eps*eps/9+5*eps**3/81
    fT=a**3/(2*B**3*M)
    H=rho*fT/det
    z=B*R/(3*S-B*R)
    hess_params=[hess(f)for f in jets]
    def second(f,i,j):
        gg=grad(f);hh=hess(f)
        out=sum(inv[a,i]*inv[b,j]*hh[a][b]for a in range(3)for b in range(3))
        for a,b,u,w in itertools.product(range(3),repeat=4):
            out-=inv[a,i]*inv[b,u]*hess_params[u][w][a]*inv[w,j]*gg[b]
        return out
    value=second(H,1,1)-2*second(H*z,0,1)+second(H*z*z,0,0)
    return {'point':list(map(str,point)),'compatibility_zero':not value,'compatibility_divided_by_H':str(value/H.c[0])}

records=[point_test(point)for point in [(1,2,3),(2,1,3),(2,3,1)]]
(HERE/'hol_potential_seed.json').write_text(json.dumps({'formula':'partial_r^2 H-2partial_Lpartial_r(zH)+partial_L^2(z^2H)','records':records,'scope':'Tests only the connection-free mixed current F(omega0 alongr-omega1 alongL); no general coupled-current exclusion.'},indent=2)+'\n')
print(json.dumps(records,indent=2))
