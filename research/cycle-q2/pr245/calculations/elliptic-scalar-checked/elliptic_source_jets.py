"""Independent exact Q dual arithmetic for normalized central forcing at y=T=u=1."""
from fractions import Fraction as Q
class Jet:
    # Taylor coefficients through degree two; enough for differentiating r_u.
    def __init__(self,v=0,d=0,d2=0):
        if isinstance(v,Jet): self.cl=v.cl
        else: self.cl=tuple(map(Q,(v,d,d2)))
    def __add__(self,z):return Jet(*(m+n for m,n in zip(self.cl,Jet(z).cl)))
    __radd__=__add__
    def __neg__(self):return Jet(*(-v for v in self.cl))
    def __sub__(self,z):return self+(-Jet(z))
    def __rsub__(self,z):return Jet(z)-self
    def __mul__(self,z):
        b=Jet(z).cl
        return Jet(*(sum(self.cl[i]*b[n-i] for i in range(n+1)) for n in range(3)))
    __rmul__=__mul__
    def inv(self):
        a,b,c=self.cl
        return Jet(1/a,-b/a**2,b*b/a**3-c/a**2)
    def __truediv__(self,z):return self*Jet(z).inv()
    def __rtruediv__(self,z):return Jet(z)*self.inv()
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        if n==0:return Jet(1)
        h=self**(n//2)
        return h*h*(self if n%2 else 1)
    def diff(self):
        a,b,c=self.cl
        return Jet(b,2*c)
    def val(self):return self.cl[0]


def evaluate(y0,t0,u0):
    u=Jet(u0,1); t,y=map(Jet,(t0,y0))
    a,b,c,d,e,f=1/t+u**6*t**3,1+y**6,t+1/t,u*y/2,y/2,u/2
    A=a*e**2*f+b*d*f**2+c*d**2*e
    B=-(27*a*a*b*b*c*c+4*a*a*c*e**3+4*a*b*b*f**3+6*a*b*c*d*e*f+4*b*c*c*d**3-d*d*e*e*f*f)/4
    E=(9*a*b*c-d*e*f)/2
    F=a*b*e*f**2+a*c*d*e**2+b*c*d**2*f
    r=B**2/A**3
    l=2*F/B-3*E/A
    l2=2*(-A/(6*B)-(F/B)**2)+3*(E/A)**2
    ru=r.diff(); re=r*l; ree=r*(l*l+l2)
    aE=E/(4*A); ar=A.diff()/(4*A*ru)
    p=4*r*(4+27*r)
    bp=(8+162*r)/p; cp=Q(15,4)/p
    L=ree-2*aE*re-bp*re**2
    M=5*aE**2-cp*re**2
    m=-u*u*y/(24*ru)
    H=m*M-(m*L).diff()/ru+ar*m*L
    for name, q in locals().copy().items():
        if name in ['A','B','ru','m','L','M','H']:print(name,q.val())
    return H.val()
if __name__=='__main__':evaluate(1,1,1)
