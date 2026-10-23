"""Second exact modular jets in the three physical variables."""
class Jet2:
    p=1000003
    def __init__(self,x,d=None,h=None):
        self.x=int(x)%self.p;self.d=[int(t)%self.p for t in (d or [0]*3)];self.h=[[int(t)%self.p for t in row] for row in (h or [[0]*3 for _ in range(3)])]
    def __add__(a,b):
        if not isinstance(b,Jet2):b=Jet2(b)
        return Jet2(a.x+b.x,[a.d[i]+b.d[i] for i in range(3)],[[a.h[i][j]+b.h[i][j] for j in range(3)] for i in range(3)])
    __radd__=__add__
    def __neg__(a):return Jet2(-a.x,[-t for t in a.d],[[-t for t in row] for row in a.h])
    def __sub__(a,b):return a+-b if isinstance(b,Jet2) else a+(-b)
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,Jet2):b=Jet2(b)
        return Jet2(a.x*b.x,[a.d[i]*b.x+a.x*b.d[i] for i in range(3)],[[a.h[i][j]*b.x+a.d[i]*b.d[j]+a.d[j]*b.d[i]+a.x*b.h[i][j] for j in range(3)] for i in range(3)])
    __rmul__=__mul__
    def __pow__(a,n):
        p=a.p;x=pow(a.x,n,p);c=n*pow(a.x,n-1,p)%p if n else 0;cc=n*(n-1)*pow(a.x,n-2,p)%p if n not in (0,1) else 0
        return Jet2(x,[c*t for t in a.d],[[c*a.h[i][j]+cc*a.d[i]*a.d[j] for j in range(3)] for i in range(3)])
    def __truediv__(a,b):return a*(b**-1) if isinstance(b,Jet2) else a*Jet2(b)**-1
    def __rtruediv__(a,b):return b*a**-1

def evaluate(poly,args):
    maxima=[max((e[i] for e,c in poly.d),default=0) for i in range(len(args))]
    powers=[[Jet2(1)] for _ in args]
    for i in range(len(args)):
        for _ in range(maxima[i]):powers[i].append(powers[i][-1]*args[i])
    out=Jet2(0)
    for e,c in poly.d:
        term=Jet2(c)
        for i,n in enumerate(e):term*=powers[i][n]
        out+=term
    return out
