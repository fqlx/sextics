"""Rank of the C-cyclic section on the plane sextic at one good mod-p point.

Polynomial basis checks use only monomials through degree 8.
The 25 by 25 connection uses division by the two fixed gradient polynomials.
"""
from collections import defaultdict
from argparse import ArgumentParser
import numpy as np

args=ArgumentParser()
args.add_argument('--prime',type=int,default=101)
args.add_argument('--value',type=int,nargs=3,default=(2,3,5))
settings=args.parse_args()
p=settings.prime
a,b,c=settings.value
def norm(q):
    return {m:n%p for m,n in q.items() if n%p}
def shift(q,i,j,s=1):
    return {(x+i,y+j):n*s%p for (x,y),n in q.items()}
def plus(q,r,s=1):
    out=dict(q)
    for m,n in r.items(): out[m]=(out.get(m,0)+s*n)%p
    return norm(out)
def deriv(q,i):
    return {(x-(i==0),y-(i==1)):n*(x if i==0 else y)%p
            for (x,y),n in q.items() if (x if i==0 else y)}
F={(0,6):a,(6,0):b,(1,1):1,(1,0):1,(0,1):1,(0,0):c}
FX,FY=deriv(F,0),deriv(F,1)
I=[(i,j) for i in range(5) for j in range(5)]
N=25
def rank(M,inv=False):
    M=np.array(M,dtype=np.int64)%p
    nr,nc=M.shape
    if inv: M=np.concatenate((M,np.eye(nr,dtype=np.int64)),axis=1)
    k=0
    for j in range(nc):
        h=np.flatnonzero(M[k:,j])
        if not len(h): continue
        i=k+h[0]
        M[[k,i]]=M[[i,k]]
        M[k]=M[k]*pow(int(M[k,j]),-1,p)%p
        f=M[:,j].copy(); f[k]=0
        M=(M-f[:,None]*M[k])%p
        k+=1
        if k==nr:break
    if inv:
        assert k==nr
        return M[:,nc:]
    return k
def vec(q,mons=I):
    assert set(q)<=set(mons)
    return [q.get(m,0)%p for m in mons]
mons=[(i,n-i) for n in range(9) for i in range(n+1)]
cols=[vec({m:1},mons) for m in I]
for n in range(1,5):
    for i in range(n+1):
        j=n-i
        u=shift(FY,i-1,j,i) if i else {}
        v=shift(FX,i,j-1,-j) if j else {}
        cols.append(vec(plus(u,v),mons))
for n in range(3):
    for i in range(n+1):cols.append(vec(shift(F,i,n-i),mons))
assert (len(cols),rank(cols))==(45,45)
print("Affine cohomology basis witness rank",rank(cols))
M,D=[],[]
for i,j in I:
    q=shift(F,i,j)
    u,v={},{}
    while True:
        h=next((m for m in q if max(m)>=5),None)
        if h is None:break
        k,l=h
        if k>=5:
            s=q[h]*pow(6*b,-1,p)%p
            q=plus(q,shift(FX,k-5,l,s),-1)
            u=plus(u,{(k-5,l):s})
        else:
            s=q[h]*pow(6*a,-1,p)%p
            q=plus(q,shift(FY,k,l-5,s),-1)
            v=plus(v,{(k,l-5):s})
    M.append(vec(q))
    D.append(vec(plus(deriv(u,0),deriv(v,1))))
M=np.array(M,dtype='int64').T
D=np.array(D,dtype='int64').T
Mi=rank(M,inv=True)
assert (Mi@M%p==np.eye(N,dtype='int64')).all()
def jets(n):
    A=[(D-np.eye(N,dtype=np.int64))@Mi%p]
    for _ in range(n):A.append(-A[-1]@Mi%p)
    W=np.zeros((n+1,N),dtype='int64')
    W[0,0]=1
    vecs=[W[0].copy()]
    for k in range(n):
        U=np.zeros((n-k,N),dtype='int64')
        for i in range(n-k):
            U[i]=(i+1)*W[i+1]
            for j in range(i+1):U[i]+=A[j]@W[i-j]
            U[i]%=p
        W=U
        vecs.append(W[0].copy())
    return vecs
vs=jets(20)
print("C-cyclic ranks", [rank(vs[:k]) for k in range(1,len(vs)+1)])

# Pivot minor and the exact mod-p coefficients of all three scalar adjoints.
basis=np.array(vs[:20],dtype='int64').T
keep=[]
for i in range(N):
    if rank(basis[keep+[i],:])>len(keep):
        keep.append(i)
    if len(keep)==20:break
B0=basis[keep,:]
V0inv=rank(B0,inv=True)
G=(D-np.eye(N,dtype='int64'))@Mi%p
unit=np.eye(N,dtype='int64')
def Vxy(x,y):return unit[:,I.index((x,y))]
def rhs(i,j,d):
    return (-(Vxy(0,0)+G@(Vxy(1,1)+Vxy(i,j)))*pow(6*d,-1,p))%p
Acol=rhs(0,1,a)
Bcol=rhs(1,0,b)
def coeff(v):
    w=V0inv@v[keep]%p
    assert (basis@w%p==v%p).all()
    return list(map(int,w))
print('20 pivot rows',keep)
print('L',coeff(vs[20]))
print('A',coeff(Acol))
print('B',coeff(Bcol))
def determinant(M):
    N=M.shape[0]
    M=M.copy()%p
    z=1
    for j in range(N):
        a=np.flatnonzero(M[j:,j])
        if not len(a):return 0
        k=j+a[0]
        if j!=k:
            z=-z;M[[k,j]]=M[[j,k]]
        v=int(M[j,j])
        z=z*v%p;M[j]=M[j]*pow(v,-1,p)%p
        for k in range(j+1,N):M[k]=(M[k]-M[k,j]*M[j])%p
    return z
print('basis det, multiplication F det, cyclic minor',determinant(np.array(cols)),determinant(M),determinant(B0))
