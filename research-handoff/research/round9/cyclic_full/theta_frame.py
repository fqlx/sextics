"""Actual theta=∇r omega0 frame, exact native rational arithmetic."""
from pathlib import Path
from functools import lru_cache
import sympy as s,pickle,json,time
from flint import fmpq_mpoly,fmpq_mpoly_ctx,fmpq
root=Path(__file__).parent;start=time.monotonic()
ctx=fmpq_mpoly_ctx.get(('L','r','x'))
class RF:
    def __init__(self,n=0,d=1):
        if isinstance(n,RF):self.n,self.d=n.n,n.d;return
        if not isinstance(n,fmpq_mpoly):n=fmpq_mpoly(str(n),ctx)
        if not isinstance(d,fmpq_mpoly):d=fmpq_mpoly(str(d),ctx)
        if not n:self.n,self.d=n,fmpq_mpoly('1',ctx);return
        assert d
        g=n.gcd(d);n=n//g;d=d//g;lc=d.leading_coefficient()
        self.n,self.d=n/lc,d/lc
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
    def __pow__(a,n):return RF(a.n**n,a.d**n)if n>=0 else RF(a.d**(-n),a.n**(-n))
    def diff(a,v):return RF(a.n.derivative(v)*a.d-a.n*a.d.derivative(v),a.d*a.d)
    def json(a):return {'numerator':str(a.n),'denominator':str(a.d)}
zero,one=RF(0),RF(1)
vars={v:RF(v)for v in ('L','r','x')}
@lru_cache(None)
def convert(e):
    if e.is_Rational:return RF(fmpq(int(e.p),int(e.q)))
    if e.is_Symbol:return vars[str(e)]
    if e.is_Add:return sum((convert(x)for x in e.args),zero)
    if e.is_Mul:
        a=one
        for x in e.args:a=a*convert(x)
        return a
    if e.is_Pow:return convert(e.base)**int(e.exp)
    raise TypeError(e)
def mul(A,B):return [[sum((A[i][k]*B[k][j]for k in range(len(B))),zero)for j in range(len(B[0]))]for i in range(len(A))]
def add(A,B):return [[a+b for a,b in zip(ar,br)]for ar,br in zip(A,B)]
data=pickle.loads((root/'actual_fast.pickle').read_bytes())
N={v:[[convert(e)for e in row]for row in data['connection'][v].tolist()]for v in ('L','r','x')}
P=[[one,zero,zero],[zero,one,zero],N['r'][0]]
u,v,w=P[2];inv=[[one,zero,zero],[zero,one,zero],[-u/w,-v/w,one/w]]
assert all(not(z.n-(one if i==j else zero).n) for i,row in enumerate(mul(P,inv))for j,z in enumerate(row))
out={};summary={}
for base in ('L','r','x'):
    dP=[[e.diff(base)for e in row]for row in P]
    left=add(dP,mul(P,N[base]));out[base]=mul(left,inv)
    assert all(not(a-b).n for ar,br in zip(mul(out[base],P),left)for a,b in zip(ar,br))
    den=ctx.constant(1)
    for row in out[base]:
        for e in row:den=den*e.d//den.gcd(e.d)
    summary[base]=dict(common_denominator=str(den),factors=[{'factor':str(f),'exponent':int(e)}for f,e in den.factor()[1]],
                       matrix=[[e.json()for e in row]for row in out[base]])
    print(base,summary[base]['factors'],time.monotonic()-start,flush=True)
old_den=ctx.constant(1)
for mat in N.values():
    for row in mat:
        for entry in row:old_den=old_den*entry.d//old_den.gcd(entry.d)
old_factors=[{'factor':str(f),'exponent':int(e)}for f,e in old_den.factor()[1]]
ans=dict(frame='(omega0,omega1,theta=∇r omega0)',convention='rows are basis derivatives; coefficient vector uses transpose',
         old_denominator_factors=old_factors,
         gauge_verified_exact=True,old_eta_coefficient_w=w.json(),new_connection=summary,seconds=time.monotonic()-start)
(root/'theta_frame.json').write_text(json.dumps(ans,indent=2)+'\n')
(root/'theta_frame.pickle').write_bytes(pickle.dumps(dict(P=[[e.json()for e in row]for row in P],connection={v:[[e.json()for e in row]for row in mat]for v,mat in out.items()},context_names=('L','r','x'))))
print(json.dumps({k:v for k,v in ans.items()if k!='new_connection'},indent=2))
