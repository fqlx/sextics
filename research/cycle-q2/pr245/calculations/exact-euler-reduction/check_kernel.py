"""Verify generic genus-ten kernel identities in the Laurent ring Q[I,b^±,T^±]."""
from fractions import Fraction as Q
class L(dict):
    def __init__(self,x=0):
        super().__init__(x if isinstance(x,dict) else ({(0,0,0):Q(x)} if x else {}))
    def __add__(self,v):
        w=L(self)
        for e,a in L(v).items():
            w[e]=w.get(e,0)+a
            if not w[e]:del w[e]
        return w
    __radd__=__add__
    def __neg__(self):return L({e:-c for e,c in self.items()})
    def __sub__(self,v):return self+-L(v)
    def __rsub__(self,v):return L(v)+-self
    def __mul__(self,v):
        r=L()
        for e,a in self.items():
            for f,c in L(v).items():
                q=tuple(x+y for x,y in zip(e,f));r=r+L({q:a*c})
        return r
    __rmul__=__mul__
    def __pow__(self,k):
        if k<0:
            assert len(self)==1
            e,v=next(iter(self.items()))
            return L({tuple(k*x for x in e):Q(v)**k})
        a=L(1)
        for _ in range(k):a=a*self
        return a
I=L({(1,0,0):1});b=L({(0,1,0):1});T=L({(0,0,1):1})
J=(1+b**3)*T**-1+T+I**6*T**3*b**-9+Q(1,2)*I*b**-1
pt=4*I**6*T**3+2*b**9*T+Q(1,2)*I*b**8-J*b**9
pb=9*b**8*T**2+(4*I*b**7-9*J*b**8)*T+12*b**11+9*b**8
pi=6*I**5*T**4+Q(1,2)*b**8*T
h=6-6*T**2+I*T*b**-1
k=-12*b**6-8*b**9-Q(11,3)*I*b**5*T+6*J*b**6*T
dl=-pb*b**-2-2*T*pt*b**-3
assert not (b*pb+3*T*pt+Q(1,2)*b**9*h)
assert not (k-Q(10,3)*T*pt*b**-3+Q(4,3)*dl)
assert not (dl+5*b**6*T**2+I*b**5*T-3*J*b**6*T+4*b**9+b**6)
target=16*I**-1*b**6+4*I**-1*b**9+Q(13,3)*b**5*T-8*J*I**-1*b**6*T
assert not (-Q(10,3)*pi*b**-3-target+4*I**-1*dl)
print('All generic genus-ten identities verified in Q[I,b^±1,T^±1], including the I and J transports and rational corrections.')
