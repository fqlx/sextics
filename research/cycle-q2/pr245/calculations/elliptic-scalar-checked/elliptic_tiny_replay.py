"""Elementary integer elimination at y=T=u=1 mod 101, independent of algebra packages."""
from itertools import product
from fractions import Fraction
from elliptic_source_jets import evaluate
P=101
half=pow(2,-1,P)
def mons(n):return [(i,j,n-i-j) for i in range(n+1) for j in range(n+1-i)]
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def unit(i):return tuple(int(j==i) for j in range(3))
def minus(a,b):return tuple(x-y for x,y in zip(a,b))
g=[((3,0,0),2,6,30),((0,3,0),2,0,0),((0,0,3),2,0,0),((2,1,0),half,half,0),((0,2,1),half,0,0),((1,0,2),half,half,0)]
def matrix(n):
    m=mons(n);size=len(m)
    B=[[0]*size for _ in m]; Bu=[[0]*size for _ in m]; deriv=[]
    for col,k in enumerate(m):
        i=next((i for i in range(3) if k[i]>=2),None)
        if i is None:
            for z,_,c1,c2 in g:
                j=m.index(z);B[j][col]=c1;Bu[j][col]=c2
            deriv.append(None)
        else:
            h=minus(minus(k,unit(i)),unit(i))
            for z,c0,c1,_ in g:
                if z[i]:
                    j=m.index(plus(h,minus(z,unit(i))))
                    B[j][col]+=z[i]*c0; Bu[j][col]+=z[i]*c1
            deriv.append((h[i],minus(h,unit(i))) if h[i] else None)
    return B,Bu,deriv
def solve(M,h):
    a=[[(x%P) for x in row]+[b%P] for row,b in zip(M,h)]
    n=len(a)
    for k in range(n):
        j=next(j for j in range(k,n) if a[j][k]);a[j],a[k]=a[k],a[j]
        q=pow(a[k][k],-1,P);a[k]=[z*q%P for z in a[k]]
        for j in range(n):
            if j!=k and a[j][k]:
                q=a[j][k];a[j]=[(v-q*w)%P for v,w in zip(a[j],a[k])]
    return [r[-1] for r in a]
def multiply(M,X):return [sum(v*w for v,w in zip(row,X))%P for row in M]
def residual(M,h,X):return [(b-a)%P for b,a in zip(h,multiply(M,X))]
def divergence(C,X,order,degree):
    basis=mons(degree); v=[0]*len(basis)
    for entry,h in zip(C,X):
        if entry:
            cf,m=entry;i=basis.index(m);v[i]=(v[i]+cf*h*pow(order,-1,P))%P
    return v
N=[0]*28;Nu=N[:]
k=mons(6).index((2,2,2));N[k]=-half;Nu[k]=-1
M,Mu,C=matrix(6)
X=solve(M,N);Xu=solve(M,residual(Mu,Nu,X))
h=divergence(C,X,2,3);hu=divergence(C,Xu,2,3)
M,Mu,C=matrix(3)
Y=solve(M,h);Yu=solve(M,residual(Mu,hu,Y))
a=divergence(C,Y,1,0)[0]
bu=Yu[mons(3).index((1,1,1))]
ru=(37202485247*pow(27648,-1,P))%P
result=(a+bu)*pow(6*ru,-1,P)%P
expected=evaluate(1,1,1)
print('Macaulay rational-coefficient specialized formula gives',result,'mod',P)
assert result==expected.numerator*pow(expected.denominator,-1,P)%P
