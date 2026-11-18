"""Good reduction test of the strict transform of D on the cone over S."""
from flint import nmod_poly,nmod_mat
from math import prod
from itertools import combinations
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('--prime',type=int,default=1009)
p=parser.parse_args().prime
def poly(cs): return nmod_poly(cs,p)
z=poly([0,1]); one=poly([1]); zero=poly([])
h=[-5,1,-3,14]; g=[[3,0,1],[1,3,0],[0,1,3],[1,0,1]]
d=[c*z-1 for c in h]
w=[prod(d[:i]+d[i+1:]) for i in range(4)]
L=[sum((h[i]*w[i]*g[i][j] for i in range(4)),zero) for j in range(3)]
assert L[0].gcd(L[1]).gcd(L[2])==z
L=[l//z for l in L]
assert L[0].gcd(L[1]).gcd(L[2])==one
def matrices(excluded):
    i,j=[a for a in range(3) if a!=excluded]
    def from_vec(s):
        t=[zero]*3
        t[s]=L[excluded]
        t[excluded]=-L[s]
        base=[sum((c*v for c,v in zip(row,t)),zero) for row in g]
        for a,dd in zip(base,d): assert (a%dd).is_zero()
        A,B,C,D=[a//dd for a,dd in zip(base,d)] # these equal 6*A, etc.
        m,n,u=t
        Q,Y=-(m+n),-(n+u)
        return [A,B,C,D,Q,Y,6*m,6*n,6*u]
    # each entry is represented as coefficient of V and coefficient of U
    return list(zip(from_vec(j),from_vec(i)))
def systems(x,cols):
    v=[poly([int(a(x)),int(b(x))]) for a,b in cols]
    A,B,C,D,Q,Y,m,n,u=v
    return [64*m**6-A**3*B*D*Q,64*n**6-B**3*C*Q*Y,64*u**6-C**3*A*D*Y]
def resultant(f,g):
    f,g=list(f),list(g)
    f=[0]*(7-len(f))+f[::-1]
    g=[0]*(7-len(g))+g[::-1]
    return int(nmod_mat([[0]*i+f+[0]*(5-i) for i in range(6)]+[[0]*i+g+[0]*(5-i) for i in range(6)],p).det())
def interp(v):
    ans=zero; term=one; n=len(v)
    for i in range(n):
        ans+=term*v[0]
        v=[(b-a)%p for a,b in zip(v,v[1:])]
        term=term*(z-i)*pow(i+1,-1,p)
    return ans
common=None
for excluded in range(3):
    cols=matrices(excluded)
    triples=[systems(i,cols) for i in range(146)]
    assert all(max(v.degree() for v in c)<=2 for c in cols)
    res=[]
    for i,j in combinations(range(3),2):
        vals=[resultant(t[i],t[j]) for t in triples]
        f=interp(vals[:145]) # each resultant uses 12 coefficients of degree <=12
        assert f(145)==vals[145]
        res.append(f)
    G=res[0].gcd(res[1]).gcd(res[2])
    common=G if common is None else common.gcd(G)
    print('pivot',excluded,'minor',L[excluded],'res degrees',[f.degree() for f in res],'common factors',G.factor(),flush=True)
print('global lambda candidates',common.factor(),flush=True)
assert common==one
from flint import nmod_mpoly_ctx
ctx=nmod_mpoly_ctx.get(('m','n','u'),p)
m,n,u=ctx.gens()
A,B,C,D,Q,Y=[-(3*m+u),-(m+3*n),-(n+3*u),-(m+u),-(m+n),-(n+u)]
eqs=[64*(6*m)**6-A**3*B*D*Q,64*(6*n)**6-B**3*C*Q*Y,64*(6*u)**6-C**3*A*D*Y]
def triples(deg): return [(a,b,deg-a-b) for a in range(deg+1) for b in range(deg-a+1)]
indices={t:i for i,t in enumerate(triples(16))}
mat=[]
for eq in eqs:
    for h in triples(10):
        row=[0]*len(indices)
        for t,c in eq.to_dict().items(): row[indices[tuple(a+b for a,b in zip(t,h))]]=int(c)
        mat.append(row)
rank=nmod_mat(mat,p).rank()
assert rank==len(indices)
print('lambda=0 homogeneous degree-16 rank',rank,'of',len(indices),flush=True)
