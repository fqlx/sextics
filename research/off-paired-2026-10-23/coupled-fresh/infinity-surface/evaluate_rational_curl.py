#!/usr/bin/env python3
"""Exact check whether the explicit rational partial curl already closes.

This evaluates the actual implicit branch and B12 on its retained density.
It is a check of this current, not a nonexistence calculation.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

N=6
class Jet:
    def __init__(self,v=0):self.v=(list(v)+[Q(0)]*(N+1))[:N+1] if isinstance(v,(tuple,list)) else [Q(v)]+[Q(0)]*N
    def __add__(self,w):
        w=jj(w);return Jet([a+b for a,b in zip(self.v,w.v)])
    __radd__=__add__
    def __neg__(self):return Jet([-a for a in self.v])
    def __sub__(self,w):return self+-jj(w)
    def __rsub__(self,w):return jj(w)+-self
    def __mul__(self,w):
        w=jj(w);return Jet([sum(self.v[k]*w.v[n-k] for k in range(n+1)) for n in range(N+1)])
    __rmul__=__mul__
    def inv(self):
        out=[1/self.v[0]]
        for n in range(1,N+1):out.append(-sum(self.v[k]*out[n-k] for k in range(1,n+1))/self.v[0])
        return Jet(out)
    def __truediv__(self,w):return self*jj(w).inv()
    def __rtruediv__(self,w):return jj(w)*self.inv()
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        ans=Jet(1)
        for _ in range(n):ans=ans*self
        return ans
    def d(self):return Jet([(n+1)*self.v[n+1] for n in range(N)]+[Q(0)])
def jj(x):return x if isinstance(x,Jet) else Jet(x)


def main():
    C=Jet([Q(1),Q(1)]);z=Q(1);H=Q(969,64);a=Jet(1)
    def q(a):return 3*C-Q(3,2)*a*z
    def P(a):return a**4+q(a)**6+a*a*(z**6+q(a)*z/2+1-H)
    def Pa(a):return 4*a**3-9*z*q(a)**5+2*a*(z**6+q(a)*z/2+1-H)-Q(3,4)*a*a*z*z
    for _ in range(4):a=a-P(a)/Pa(a)
    assert all(t==0 for t in P(a).v)
    qq=q(a)
    J=qq**2*(36*H*(a*z+qq)-24*a*a*qq-21*a*qq*z*z-144*a*z**7-36*a*z-17*qq*qq*z-72*qq*z**6-36*qq)/(12*Pa(a))
    def theta(f):return C*f.d()
    def affine(f,A,B):return A*theta(f)+B*f
    def B12(f):
        g=affine(affine(affine(f,1,-2),1,-1),2,3)
        return (C**3/H**2*(44*theta(theta(g))-35*g)-729*H**2/C**3*(11*theta(theta(g))-39*g))/630
    value=(-B12(theta(J))/(9*H**2)).v[0]
    result={'actual_point':{'a':'1','C':'1','z':'1','H':'969/64'},'implicit_C_jet_order':N,'P_on_jet_is_zero':True,
        'operator':'B12, exact right-to-left Euler composition with all implicit a(C) derivatives',
        'retained_remainder':str(value),'partial_current_closed_at_point':value==0,
        'scope':'Check of this explicit rational partial current only. No all-pole or ansatz exclusion follows.'}
    Path(__file__).with_name('rational-curl-point-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
