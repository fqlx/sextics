"""Independent Leibniz-rule audit of the complete two-section adjoint rows."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json,math
import sympy as s
c,d,e=s.symbols('c d e');xs=(c,d,e);zero=(0,0,0)
def clean(P):return {a:s.factor(b)for a,b in P.items()if s.factor(b)!=0}
def add(*Ps):
    out=defaultdict(lambda:0)
    for P in Ps:
        for a,b in P.items():out[a]+=b
    return clean(out)
def scale(v,P):return clean({a:v*b for a,b in P.items()})
def mul(f):return {zero:f}
def compose(P,Q):
    out=defaultdict(lambda:0)
    for aa,cc in P.items():
        for bb,dd in Q.items():
            for gg in product(*(range(n+1)for n in aa)):
                factor=math.prod(math.comb(n,k)for n,k in zip(aa,gg))
                deriv=dd
                for x,n in zip(xs,gg):deriv=s.diff(deriv,x,n)
                exponent=tuple(n-k+m for n,k,m in zip(aa,gg,bb))
                out[exponent]+=factor*cc*deriv
    return clean(out)
def prod(*Ps):
    out=mul(1)
    for P in Ps:out=compose(out,P)
    return out
def adjoint(P):
    return add(*(scale((-1)**sum(aa),compose({aa:1},mul(cc)))for aa,cc in P.items()))
def equal(P,Q):return not add(P,scale(-1,Q))
def shift(P,v):return add(P,mul(v))
C={(1,0,0):1};D={(0,1,0):1};E={(0,0,1):1}
A={(1,0,0):-c/3,(0,1,0):-2*d/3,(0,0,1):-e/6}
B={(1,0,0):-c/3,(0,1,0):-d/6,(0,0,1):-e/6}
T={(1,0,0):-c/3,(0,1,0):-d/6,(0,0,1):-2*e/3}
R=s.Rational
P=[add(prod(E,E),scale(-1,prod(shift(T,R(1,6)),C))),
   add(prod(D,D),scale(-1,prod(shift(A,-R(1,3)),C))),
   add(prod(A,shift(B,-R(1,2)),shift(T,R(1,2))),scale(-1,prod(C,C,C)))]
Q=[P[0],
   add(prod(D,D),scale(-1,prod(shift(A,-R(5,6)),C))),
   add(prod(shift(A,-R(1,2)),B,shift(T,R(1,2))),scale(-1,prod(C,C,C)))]
Pstar=[add(prod(E,E),scale(-1,prod(C,shift(T,-R(4,3))))),
       add(prod(D,D),scale(-1,prod(C,shift(A,-R(5,6))))),
       add(prod(C,C,C),scale(-1,prod(shift(A,-R(7,6)),shift(B,-R(1,6)),shift(T,-R(5,3)))))]
Qstar=[Pstar[0],
       add(prod(D,D),scale(-1,prod(C,shift(A,-R(1,3))))),
       add(prod(C,C,C),scale(-1,prod(shift(A,-R(2,3)),shift(B,-R(2,3)),shift(T,-R(5,3)))))]
Lz=[prod(C,C),prod(C,E),prod(shift(A,-R(1,6)),E),prod(A,shift(T,R(1,2)))]
Lx=[prod(shift(B,-R(1,6)),E),prod(B,shift(T,R(1,2))),prod(C,C),prod(C,E)]
Lzstar=[prod(C,C),prod(C,E),prod(E,shift(A,-1)),prod(shift(T,-R(5,3)),shift(A,-R(7,6)))]
Lxstar=[prod(E,shift(B,-R(1,2))),prod(shift(T,-R(5,3)),shift(B,-R(2,3))),prod(C,C),prod(C,E)]
checks={}
for prefix,primal,dual in [('zeta_self',P,Pstar),('xi_self',Q,Qstar),('cross_zeta',Lz,Lzstar),('cross_xi',Lx,Lxstar)]:
    for j,(pr,ad)in enumerate(zip(primal,dual),1):checks[f'{prefix}_{j}']=equal(adjoint(pr),ad)
shift_inf=d*(c-d*d/4)/2
for j,L in enumerate(Q+Lx,1):
    checks[f'infinity_adjoint_{j}']=equal(adjoint(prod(L,mul(shift_inf))),prod(mul(shift_inf),adjoint(L)))
checks['closed_cross_companion']=equal(prod(Lxstar[0],shift(T,-1)),prod(Lxstar[1],E))
checks['closed_cross_scalar_heat_image']=equal(
    add(prod(Lzstar[0],shift(T,-1)),scale(-1,prod(Lzstar[1],E))),scale(-1,prod(Pstar[0],C)))
assert all(checks.values()),checks
out={'checks':checks,'passed':True,
 'source_equation':'the (Z),(X) operators in ruling-source/COUPLED-TORIC-ADJOINT.md agree with automatic formal adjoints',
 'infinity':'all seven xi rows include the complete operator on s*omega; adjoint residual equals s times xi residual',
 'certificate':False}
Path(__file__).with_name('coupled-toric-adjoint-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
