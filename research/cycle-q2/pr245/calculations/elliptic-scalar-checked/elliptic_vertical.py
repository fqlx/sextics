"""Complete vertical K3-pole rational current test in true Weierstrass coordinates, F101."""
from elliptic_good_fibre import P,Poly,gcd
def rank(rows):
    rows=[list(t) for t in rows]; n=len(rows[0]); piv=[]; m=len(rows)
    for k in range(n):
        z=next((j for j in range(len(piv),m) if rows[j][k]%P),None)
        if z is None:continue
        j=len(piv);rows[j],rows[z]=rows[z],rows[j]
        c=pow(rows[j][k]%P,-1,P)
        rows[j]=[(v*c)%P for v in rows[j]]
        for h in range(m):
            if h!=j and rows[h][k]%P:
                c=rows[h][k]%P
                rows[h]=[(x-c*y)%P for x,y in zip(rows[h],rows[j])]
        piv.append(k)
    return len(piv),piv,rows
def vertical(y,t):
    u=Poly([0,1]); half=pow(2,-1,P)
    div=lambda n:pow(n,-1,P)
    a,b,c,d,e,f=div(t)+u**6*t**3,1+y**6,t+div(t),u*y*half,y*half,u*half
    A=a*e**2*f+b*d*f**2+c*d**2*e
    B=-(27*a*a*b*b*c*c+4*a*a*c*e**3+4*a*b*b*f**3+6*a*b*c*d*e*f+4*b*c*c*d**3-d*d*e*e*f*f)*div(4)
    D=4*A**3+27*B**2
    assert len(D)==25 and gcd(D,D.der())==Poly(1)
    Ae=(9*a*b*c-d*e*f)*half
    Be=a*b*e*f**2+a*c*d*e**2+b*c*d**2*f
    Bee=-A*div(6)
    De=12*A*A*Ae+54*B*Be
    la=lambda w,v: -A*A*w-9*half*B*v
    mu=lambda w,v:9*half*B*w-3*A*v
    Le,Me=la(Ae,Be),mu(Ae,Be)
    dLe=-2*A*Ae**2-9*half*(Be**2+B*Bee)
    dMe=3*half*Ae*Be-3*A*Bee
    factor= -u*u*y*div(24)
    target=(factor*(dLe*D-Le*De+Le**2+A*div(3)*Me**2),factor*(dMe*D-Me*De))
    Lu,Mu=la(A.der(),B.der()),mu(A.der(),B.der())
    def col(p,q):
        return (D*p.der()+(Lu-D.der())*p+A*div(3)*Mu*q,D*q.der()+(-Lu-D.der())*q+Mu*p)
    cols=[col(u**k,Poly()) for k in range(27)]+[col(Poly(),u**k) for k in range(23)]+[target]
    sizes=[max(len(c[i]) for c in cols) for i in range(2)]
    rows=[[c[i][k] if k<len(c[i]) else 0 for c in cols] for i,size in enumerate(sizes) for k in range(size)]
    k,piv,red=rank(rows)
    ordinary=sum(z!=50 for z in piv)
    print('base y,T, mod p; degrees; rational input and augmented ranks:',(y,t),P,sizes,ordinary,k,flush=True)
    return ordinary,k
if __name__=='__main__':vertical(2,3)
