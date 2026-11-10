from pathlib import Path
import sympy as s, json, re, time
from flint import fmpq_mpoly_ctx
b,c,d,u,z,t=s.symbols('b c d u z t');q=1+2*b-u;r=c*c+2*c*d-z*u
H=(q*q*r+2*q*r*r)/7
terms={(0,0):(1-u)*(c*c-z*u)*(1-u+2*c*c-2*z*u)/7,(2,0):4*(c*c-z*u)/7,(0,2):8*c*c*(1-u)/7,(1,1):8*c*(1-u+2*c*c-2*z*u)/7,(1,0):4*(c*c-z*u)*(1-u+c*c-z*u)/7,(0,1):2*c*(1-u)*(1-u+4*c*c-4*z*u)/7,(1,2):16*c*c/7,(2,1):8*c/7}
assert s.expand(H-sum(b**i*d**j*h for (i,j),h in terms.items()))==0
F0=b**6+d**6+2*(1+z**3)*u**3+30*(1+z**2*c*c)*u*u+30*(1+z*c**4)*u+2*(1+c**6)
raw=(2+b**6+2*c**6+d**6+30*u+30*u*u+2*u**3+30*z*c**4*u+30*z*z*c*c*u*u+2*z**3*u**3+s.Rational(5,7)*q*q*r+s.Rational(10,7)*q*r*r)
assert s.expand(raw-F0-5*H)==0
assert s.discriminant(F0.subs({b:0,d:0,z:1,c:0}),u)==289872
# Abstract normal-commutator, treating each P and f as arbitrary.
x,y=s.symbols('x y');f=s.Function('f')(u);P=s.Function('P')(u);Q=s.Function('Q')(x,u);g=s.diff(f+t*P,u);a=s.Function('a')(x,y,u,t)
D=lambda w:s.diff(w,t)-P*s.diff(w,u)/g
Dx=lambda w:s.diff(w,x)-3*x*x*s.diff(w,u)/g
Dy=lambda w:s.diff(w,y)-2*y*s.diff(w,u)/g
L=lambda w:s.diff(w/g,u)/g
assert s.simplify(D(Dx(a))-Dx(D(a)))==0 and s.simplify(D(Dy(a))-Dy(D(a)))==0
assert s.simplify(D(L(Q))-L(-s.diff(P*Q/g,u)))==0
# Verify the four odd-sector coordinate bridges as exact chain rules.
GX,GY,GU,GX_u,GY_u=s.symbols("GX GY GU GX_u GY_u")
# X=d²,Y=b³ and X=b²,Y=d³ give the same factor by swapping b,d.
g0=s.symbols("g0",nonzero=True)
for bb,dd in [(b,d),(d,b)]:
 lhs=(2*dd/3)*(3*bb**2*GY-6*bb**5*GY_u/g0)+bb**2*(2*dd*GX-6*dd**5*GX_u/g0)
 rhs=2*bb**2*dd*(GX-3*dd**4*GX_u/g0+GY-2*bb**3*GY_u/g0)
 assert s.factor(lhs-rhs)==0
# The remaining three i+j=2 characters are solved by radial Euler divergence.
ff=s.Function("ff")(u);rr=s.Function("rr")(u);ggg=s.diff(ff,u);AA=rr/(3*ff*ggg)
assert s.simplify(6*AA+6*ff*s.diff(AA,u)/ggg-2*s.diff(rr/ggg,u)/ggg)==0
# Independently replay exact giant current in the published coefficient ring.
obj=json.load(open(Path(__file__).resolve().parent / 'weierstrass-normal-current-exact.json'));names=('omega','Y','X','u','beta','B0','C0','D0','h0','h1','h2','k0','k1');ctx=fmpq_mpoly_ctx.get(names);gens=dict(zip(names,ctx.gens()))
def parse(expr):
 parts=re.findall(r'[+-]?\s*[^+-]+',expr);out=ctx.constant(0)
 for p in parts:
  p=p.strip();sign=-1 if p.startswith('-') else 1;p=p.lstrip('+-').strip();value=ctx.constant(sign)
  for factor in p.split('*'):
   factor=factor.strip()
   if not factor:continue
   if '^' in factor:
    v,n=factor.split('^');value*=gens[v.strip()]**int(n)
   elif factor in gens:value*=gens[factor]
   else:value*=int(factor)
  out+=value
 return out
F=parse(obj['surface']);nX=parse(obj['gamma_X_numerator']);nY=parse(obj['gamma_Y_numerator']);den=parse(obj['common_denominator']);Q=parse(obj['source_Q']);w,Y,X,uu,beta,B0,C0,D0,h0,h1,h2,k0,k1=ctx.gens();gg=F.derivative(3);gup=gg.derivative(3)
def numpartial(numer,j):return numer.derivative(j)*den-numer*den.derivative(j)
defect=gg**3*(numpartial(nX,2)+numpartial(nY,1))-gg**2*(3*X*X*numpartial(nX,3)+2*Y*numpartial(nY,3))-(gg*Q.derivative(3)-gup*Q)*den*den
# Reduce both defining equations. Note denominator is already g*Den.
cyclo=w*w+w+1;defect=divmod(defect,cyclo)[1];rem=divmod(defect,F)[1];assert rem==0
print('PASS all eight original source sectors, protected target binding, normal commutators, and literal generic Weierstrass quotient.')
