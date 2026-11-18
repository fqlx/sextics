"""Physical elliptic reduction of the exact residual; finite arithmetic circuit over Q(y,T,u)."""
import itertools
import json
import sympy as s

x, p, z, y, T, u = s.symbols('x p z y T u')
coords = (x, p, z)
a = 1/T + u**6*T**3
b = 1+y**6
c = T+1/T
d,e,f = u*y/2, y/2, u/2
G = a*x**3+b*p**3+c*z**3+d*x*x*p+e*p*p*z+f*z*z*x
N = (u**2/6)*x*p*z**4+(2*u/T)*x**3*p*z**2
A = a*e**2*f+b*d*f**2+c*d**2*e
B = -(27*a*a*b*b*c*c+4*a*a*c*e**3+4*a*b*b*f**3+
        6*a*b*c*d*e*f+4*b*c*c*d**3-d*d*e*e*f*f)/4
r = B**2/A**3


def mons(n):
    return [(i,j,n-i-j) for i in range(n+1) for j in range(n+1-i)]


def mon(m):
    return x**m[0]*p**m[1]*z**m[2]


def coeff(v, exps):
    h = s.Poly(v, *coords).as_dict()
    return s.Matrix([h.get(m,0) for m in exps])


def system(n):
    basis=mons(n)
    rows=[]
    columns=[]
    divs=[]
    for m in basis:
        k=next((i for i,v in enumerate(m) if v >=2),None)
        if k is None:
            assert n==3 and m==(1,1,1)
            columns.append(coeff(s.diff(G,u),basis))
            divs.append(s.Integer(0))
            rows.append(None)
        else:
            ex=list(m)
            ex[k]-=2
            q=mon(ex)
            columns.append(coeff(q*G.diff(coords[k]),basis))
            divs.append(q.diff(coords[k]))
            rows.append((k,q))
    return s.Matrix.hstack(*columns),divs, rows


def value(y0=1,T0=1,u0=1,central=False):
    pt={y:s.Rational(y0),T:s.Rational(T0),u:s.Rational(u0)}
    sub=lambda m:m.subs(pt)
    m6, div6, _ = system(6)
    m3, div3, what3=system(3)
    n6=coeff(-u**2*y*(x*p*z)**2/2 if central else N,mons(6))
    a6=sub(m6).inv()*sub(n6)
    a6u=sub(m6).inv()*(sub(n6.diff(u))-sub(m6.diff(u))*a6)
    n3=coeff(sum(q*v for q,v in zip(div6,a6))/2,mons(3))
    n3u=coeff(sum(q*v for q,v in zip(div6,a6u))/2,mons(3))
    a3=sub(m3).inv()*n3
    a3u=sub(m3).inv()*(n3u-sub(m3.diff(u))*a3)
    k=what3.index(None)
    rho=sum(q*v for q,v in zip(div3,a3))
    h,hu=a3[k],a3u[k]
    assert sub(m6)*a6==sub(n6)
    assert sub(m3)*a3==n3
    assert sub(m6)*a6u+sub(m6.diff(u))*a6==sub(n6.diff(u))
    assert sub(m3)*a3u+sub(m3.diff(u))*a3==n3u
    delta=sub(4*A**3+27*B**2)
    rr,r_u=sub(r),sub(r.diff(u))
    assert delta!=0 and r_u!=0
    # N/G³ reduces to rho·omega - h·nabla_u omega.
    # The physical differential is one sixth of this before the prescribed density change.
    physical=(rho+hu)/(6*r_u)
    return {k:str(q) for k,q in dict(m6_det=sub(m6).det(),m3_det=sub(m3).det(),disc=delta,
                                     A=sub(A),B=sub(B),r=rr,r_u=r_u,
                                     omega_coefficient=rho,minus_derivative_coefficient=h,h_u=hu,
                                     normalized_source_in_u=(rho+hu)/6,
                                     normalized_source_in_r=physical).items()}


def universal():
    X, L = s.symbols('X L')
    g=X**3+X+L
    F=3*(4+27*L**2)/4-27*L*g+s.Rational(15,4)*g**2
    co=s.symbols('a:5')
    P=sum(v*X**i for i,v in enumerate(co))
    eq=s.Poly(s.expand(P.diff(X)*g-3*P*g.diff(X)/2-F),X)
    sol=s.solve(eq.all_coeffs(),co,dict=True)[0]
    P=s.expand(P.subs(sol))
    assert s.expand(P.diff(X)*g-3*P*g.diff(X)/2-F)==0
    return str(P)


def central_source(y0=1,T0=1,u0=1):
    yt={y:s.Rational(y0),T:s.Rational(T0)}
    v={u:s.Rational(u0)}
    S=A.subs(yt)
    K=B.subs(yt)
    rr=K**2/S**3
    ru=rr.diff(u)
    ae=((9*a*b*c-d*e*f)/2).subs(yt)
    be=(a*b*e*f**2+a*c*d*e**2+b*c*d**2*f).subs(yt)
    ell=2*be/K-3*ae/S
    ell2=2*(-S/(6*K)-(be/K)**2)+3*(ae/S)**2
    re=rr*ell
    ree=rr*(ell**2+ell2)
    ar=S.diff(u)/(4*S*ru)
    az=ae/(4*S)
    denom=4*rr*(4+27*rr)
    bpf=(8+162*rr)/denom
    cpf=s.Rational(15,4)/denom
    L=ree-2*az*re-bpf*re**2
    M=5*az**2-cpf*re**2
    mass=-u**2*s.Rational(y0)/(24*ru)
    # Evaluate the only first derivative before substituting its result.
    return (mass*M).subs(v)-(mass*L).diff(u).subs(v)/ru.subs(v)+(ar*mass*L).subs(v)


if __name__=='__main__':
    from elliptic_vertical import vertical
    vertical(2,3)
    print('Universal Picard-Fuchs exact relative primitive numerator:',universal(),flush=True)
    for central in [False,True]:
        data=value(1,1,1,central)
        print('Macaulay paired-central' if central else 'Macaulay sparse residual',json.dumps(data,indent=2),flush=True)
        if central:
            val=central_source(1,1,1)
            print('Independent closed rational formula for central normalized forcing:',val,flush=True)
            assert s.Rational(data['normalized_source_in_r'])==val

    from elliptic_mixed_delta import construction
    construction()
