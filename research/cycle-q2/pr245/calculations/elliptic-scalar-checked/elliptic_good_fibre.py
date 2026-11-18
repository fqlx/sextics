"""Small exact finite-field witness for the physical elliptic K3 pencil."""
P=101
class Poly(tuple):
    def __new__(cls,x=0):
        t=[x] if isinstance(x,int) else list(x)
        while t and t[-1]%P==0:t.pop()
        return super().__new__(cls,[j%P for j in t])
    def __add__(self,q):
        q=Poly(q)
        return Poly([(self[k] if k<len(self) else 0)+(q[k] if k<len(q) else 0) for k in range(max(len(self),len(q)))])
    __radd__=__add__
    def __neg__(self):return Poly([-a for a in self])
    def __sub__(self,q):return self+(-Poly(q))
    def __rsub__(self,q):return Poly(q)-self
    def __mul__(self,q):
        q=Poly(q);w=[0]*(len(q)+len(self))
        for m,c in enumerate(self):
            for n,d in enumerate(q):w[m+n]+=c*d
        return Poly(w)
    __rmul__=__mul__
    def __pow__(self,k):
        if k==0:return Poly(1)
        h=self**(k//2)
        return h*h*(self if k%2 else 1)
    def der(self):return Poly([i*c for i,c in enumerate(self)][1:])
    def mod(self,q):
        while self and len(self)>=len(q):
            self-=q*Poly([0]*(len(self)-len(q))+[self[-1]*pow(q[-1],-1,P)])
        return self

def gcd(a,b):
    while b:a,b=b,a.mod(b)
    return a*pow(a[-1],-1,P)

u=Poly([0,1]); y=2;t=3; half=pow(2,-1,P)
a,b,c,d,e,f=pow(t,-1,P)+u**6*t**3,1+y**6,t+pow(t,-1,P),u*y*half,y*half,u*half
A=a*e**2*f+b*d*f**2+c*d**2*e
B=-(27*a*a*b*b*c*c+4*a*a*c*e**3+4*a*b*b*f**3+6*a*b*c*d*e*f+4*b*c*c*d**3-d*d*e*e*f*f)*pow(4,-1,P)
D=4*A**3+27*B**2
print('deg A,B,Delta',len(A)-1,len(B)-1,len(D)-1)
print('A',list(A),'B',list(B),'D',list(D))
print('gcd(Delta,Delta_u)',list(gcd(D,D.der())))
assert [len(A)-1,len(B)-1,len(D)-1]==[7,12,24] and gcd(D,D.der())==Poly(1)
