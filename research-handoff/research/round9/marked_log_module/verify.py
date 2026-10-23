"""Free marked log basis and exact full rank-five contractions."""
from pathlib import Path
from functools import lru_cache
import itertools,pickle,json,time,sympy as S
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
root=Path(__file__).parent;start=time.monotonic();raw=pickle.loads((root/'input.pickle').read_bytes());pars=raw['symbols'];L,r,x,s=pars
ctx=fmpq_mpoly_ctx.get(tuple(map(str,pars)))
class RF:
    def __init__(self,n=0,d=1):
        if isinstance(n,RF):self.n,self.d=n.n,n.d;return
        if not isinstance(n,fmpq_mpoly):n=fmpq_mpoly(n,ctx)if isinstance(n,str)else ctx.constant(fmpq(n))
        if not isinstance(d,fmpq_mpoly):d=fmpq_mpoly(d,ctx)if isinstance(d,str)else ctx.constant(fmpq(d))
        if not n:self.n,self.d=n,ctx.constant(1);return
        assert d;g=n.gcd(d);n=n//g;d=d//g;lc=d.leading_coefficient();self.n,self.d=n/lc,d/lc
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
    def payload(a):return dict(numerator=str(a.n),denominator=str(a.d))
zero,one=RF(0),RF(1);sy={str(p):RF(str(p))for p in pars}
@lru_cache(None)
def convert(e):
    if e.is_Rational:return RF(fmpq(int(e.p),int(e.q)))
    if e.is_Symbol:return sy[str(e)]
    if e.is_Add:return sum((convert(a)for a in e.args),zero)
    if e.is_Mul:
        ans=one
        for a in e.args:ans*=convert(a)
        return ans
    if e.is_Pow:return convert(e.base)**int(e.exp)
    raise TypeError(e)
txt=(root/'module.log').read_text();assert txt.startswith('SIZE\n5\n') and '?'not in txt
K=[[RF(txt.split('COEFF '+str(j)+' '+str(i)+'\n')[1].split('\n')[0])for i in range(1,7)]for j in range(1,6)]
MM=[[convert(v)for v in row]for row in raw['matrix'].tolist()]
for gen in K:assert all(not sum((MM[i][j]*gen[j]for j in range(6)),zero).n for i in range(2))
# Omit huge raw index2; simplify the fourth by a polynomial elementary step.
basis=[K[i]for i in (0,1,3,4)];basis[-1]=[a+(15*sy['s']-3)*b for a,b in zip(basis[-1],basis[2])]
base=[[convert(v)for v in V]for V in raw['base_fields']]
fields=[[sum((gen[j]*base[j][i]for j in range(3)),zero)for i in range(3)]+[gen[3]]for gen in basis]
P,Q=convert(raw['P']),convert(raw['Q']);D1,D2=[convert(raw['base'][k])for k in ('D1','D2')];X=sy['x'];D=X*D1*D2*P*Q
def det(A):
    ans=zero
    for perm in itertools.permutations(range(4)):
        v=one
        for i,j in enumerate(perm):v*=A[i][j]
        if sum(perm[i]>perm[j]for i in range(4)for j in range(i+1,4))%2:v=-v
        ans+=v
    return ans
dc=det([[basis[j][i]for j in range(4)]for i in range(4)])
assert not(dc+176400*P*Q).n
assert not(det([[fields[j][i]for j in range(4)]for i in range(4)])-21176820000*D).n
divisors=[X,D1,D2,P,Q];assert all(len(a.n.factor()[1])==1 and a.n.factor()[1][0][1]==1 for a in divisors)
assert all(a.n.gcd(b.n).is_constant()for i,a in enumerate(divisors)for b in divisors[i+1:])
quotients=[];divergences=[]
for gen,V in zip(basis,fields):
    quot=[]
    for div in divisors:
        dd=sum((V[i]*div.diff(str(p))for i,p in enumerate(pars)),zero)/div
        assert dd.d.is_constant();quot.append(dd)
    assert not(quot[-2]-gen[-2]).n and not(quot[-1]-gen[-1]).n
    quotients.append(quot);divergences.append(sum((V[i].diff(str(p))for i,p in enumerate(pars)),zero))

rank5_path=Path('/workspace/research/round10/horizontal5/rank5_connection.pickle');rank5=pickle.loads(rank5_path.read_bytes())
assert tuple(rank5['variables'])==tuple(map(str,pars))
N={name:[[RF(a['numerator'],a['denominator'])for a in row]for row in mat]for name,mat in rank5['connection'].items()}
contract=[];den=[]
for V in fields:
    mat=[[sum((V[k]*N[str(pars[k])][i][j]for k in range(4)),zero)for j in range(5)]for i in range(5)]
    dd=ctx.constant(1)
    for row in mat:
        for v in row:dd=dd*v.d//dd.gcd(v.d)
    den.append(str(dd));contract.append([[v.payload()for v in row]for row in mat])
    assert dd.is_constant(),str(dd)
packet=dict(variables=tuple(map(str,pars)),P=raw['P'],Q=raw['Q'],B=raw['P']/x,Delta=raw['Q']/(49*x),
            basis_coefficients=[[v.payload()for v in row]for row in basis],
            fields=[[v.payload()for v in row]for row in fields],
            field_divergences=[v.payload()for v in divergences],
            log_quotients=[[v.payload()for v in row]for row in quotients],log_quotient_order=('x','D1','D2','P','Q'),
            B_Delta_quotients=[[ (q[3]-q[0]).payload(),(q[4]-q[0]).payload()]for q in quotients],
            connection_contractions=contract,all_contractions_polynomial=True,
            determinant_constant=21176820000,divisor='x*D1*D2*P*Q',
            complete_free_basis='Exact tangencies and Saito determinant criterion for the reduced divisor.',
            graph_restriction='After s=s_eff retain combinations sum c_i*psi_i=0, psi_i=W_i(s)-sum_{j=L,r,x}W_i(j)*V_j(s_eff). Six pairwise Koszul combinations span over the physical rational function field, three on each nonzero pivot chart.',
            rank5_connection_path=str(rank5_path),seconds=time.monotonic()-start,
            scope='Complete universal marked log module and polynomial rank5 operators. No current solution or original certificate.')
(root/'verified.pickle').write_bytes(pickle.dumps(packet))
js={k:v for k,v in packet.items()if k not in ('P','Q','B','Delta','connection_contractions')};js.update(P=str(raw['P']),Q=str(raw['Q']),B=str(raw['P']/x),Delta=str(raw['Q']/(49*x)),contraction_common_denominators=den)
(root/'verified.json').write_text(json.dumps(js,indent=2)+'\n');print(json.dumps({k:v for k,v in js.items()if k not in ('fields','basis_coefficients','log_quotients','B_Delta_quotients')},indent=2))
