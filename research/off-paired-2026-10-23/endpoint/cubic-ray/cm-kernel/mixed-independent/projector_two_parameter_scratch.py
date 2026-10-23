import sympy as S
r,v,b,l=S.symbols('r v b l',nonzero=True)
D=4*b**3+27;N=(1+l)**3+b**3*l
E=(r*r+r*v+v*v+b)*(4*b*b-9*v+6*b*v*v)/D-S.Rational(1,3)
dinv=((1+l)**2-(1+l)*b*v+b*b*v*v)/N

def ut(vv):
 n,d=S.fraction(S.cancel(vv));nn=S.rem(S.Poly(n,v),S.Poly(v**3-l,v)).as_expr();return S.cancel(nn.coeff(v,0)/d)
def rr(vv):
 n,d=S.fraction(S.cancel(vv));return S.rem(S.Poly(n,r)*S.invert(S.Poly(d,r),S.Poly(r**3+b*r+1,r)),S.Poly(r**3+b*r+1,r)).as_expr()
def tf(vv):
 z=rr(vv);return rr(z-z.coeff(r,0)+S.Rational(2,3)*b*z.coeff(r,2))
V=rr(-1/(r*(b+3*r*r))-S.Rational(1,3));W=rr(b*r/(b+3*r*r)**3)
a0,a1=S.symbols('a0 a1')
def co(vv):
 sol=S.solve(S.Poly(rr(tf(vv)-a0*V-a1*W),r).all_coeffs(),[a0,a1]);return [S.factor(sol[a0]),S.factor(sol[a1])]
print('H',co(ut(E)),flush=True)
K=co(b*ut(E*v*dinv)/3);L=co(ut(E*(1+b*v/(3*l))*dinv))
print('K',K,flush=True);print('L',L,flush=True)
k=S.symbols('k',nonzero=True)
K=[z.subs(b**3,k) for z in K];L=[z.subs(b**3,k) for z in L]

def theta(z):
 A,B=z;return [S.factor(k*S.diff(A,k)+3*B/(4*k+27)),S.factor(k*S.diff(B,k)-2*A+(27-2*k)*B/(4*k+27))]
tL=theta(L)
curv=[S.factor(tL[i]-S.diff(K[i],l)) for i in range(2)]
print('curv',curv,flush=True)
