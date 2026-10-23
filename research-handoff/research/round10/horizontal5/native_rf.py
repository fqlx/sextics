"""Small exact rational field over QQ(L,r,x,s), with native FLINT polynomials."""
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
ctx=fmpq_mpoly_ctx.get(('L','r','x','s'))
class RF:
    def __init__(self,n=0,d=1):
        if isinstance(n,RF):self.n,self.d=n.n,n.d;return
        if isinstance(n,dict):n,d=n['numerator'],n['denominator']
        if isinstance(n,dict):n=ctx.from_dict({tuple(e):fmpq(c) for e,c in n.items()})
        if isinstance(d,dict):d=ctx.from_dict({tuple(e):fmpq(c) for e,c in d.items()})
        if not isinstance(n,fmpq_mpoly):n=fmpq_mpoly(str(n),ctx)
        if not isinstance(d,fmpq_mpoly):d=fmpq_mpoly(str(d),ctx)
        assert d
        if not n:self.n,self.d=n,ctx.constant(1);return
        g=n.gcd(d);n=n//g;d=d//g;lc=d.leading_coefficient();self.n,self.d=n/lc,d/lc
    def __neg__(a):return RF(-a.n,a.d)
    def __add__(a,b):
        b=RF(b);g=a.d.gcd(b.d);ad=a.d//g;bd=b.d//g
        return RF(a.n*bd+b.n*ad,a.d*bd)
    __radd__=__add__
    def __sub__(a,b):return a+-RF(b)
    def __rsub__(a,b):return RF(b)+-a
    def __mul__(a,b):
        b=RF(b);g=a.n.gcd(b.d);h=b.n.gcd(a.d)
        return RF((a.n//g)*(b.n//h),(a.d//h)*(b.d//g))
    __rmul__=__mul__
    def __truediv__(a,b):b=RF(b);return a*RF(b.d,b.n)
    def __rtruediv__(a,b):return RF(b)/a
    def __pow__(a,n):return RF(a.n**n,a.d**n) if n>=0 else RF(a.d**(-n),a.n**(-n))
    def diff(a,v):return RF(a.n.derivative(v)*a.d-a.n*a.d.derivative(v),a.d*a.d)
    def json(a):return {'numerator':str(a.n),'denominator':str(a.d)}
    def __bool__(a):return bool(a.n)
zero,one=RF(0),RF(1)
def mul(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),zero) for j in range(len(B[0]))] for i in range(len(A))]
def flatness(matrices):
    result={};names=list(matrices)
    for i,vi in enumerate(names):
        for vj in names[i+1:]:
            A,B=matrices[vi],matrices[vj];BA,AB=mul(B,A),mul(A,B)
            bad=[]
            for r in range(len(A)):
                for c in range(len(A)):
                    f=B[r][c].diff(vi)-A[r][c].diff(vj)+BA[r][c]-AB[r][c]
                    if f:bad.append((r,c,f.json()))
            result[vi+','+vj]=bad
    return result
