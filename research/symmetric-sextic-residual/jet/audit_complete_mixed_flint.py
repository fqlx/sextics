from pathlib import Path
import json,time,resource,sympy as S
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq
st=time.time();names=['u','b','d','c','z','ell','K'];syms=S.symbols(' '.join(names));env=dict(zip(names,syms));C=fmpq_mpoly_ctx.get(tuple(names));u,b,d,c,z,ell,K=C.gens();zero=C.constant(0)
def cv(e):
 P=S.Poly(e,*syms,domain=S.QQ);return C.from_dict({ex:fmpq(int(v.p),int(v.q)) for ex,v in P.terms()})
D=json.load(open(Path(__file__).resolve().parent / 'mixed-first-complete.json'));B=b**6;D6=d**6;ss=B+D6;Hb=(ss+K)**2-4*K*B;Hd=(ss+K)**2-4*K*D6;den=189*K**2*ell**2*u**5*(K+B)*(K+D6)*ss*Hb*Hd
Ns=[]
for key in ['beta_b','beta_d']:
 expr=S.sympify(D[key],locals=env);N=zero
 for term in S.Add.make_args(expr):
  n,q=S.fraction(term);qpoly=cv(q);fac,rem=divmod(den,qpoly);assert rem.is_zero();N+=cv(n)*fac
 Ns.append(N);print(key,'common numerator terms',len(N),'elapsed',round(time.time()-st,1),flush=True)
F0=B+D6+ell*u**3+K;g=3*ell*u*u;fb=6*b**5;fd=6*d**5;R=zero
for N,i,fi in zip(Ns,[1,2],[fb,fd]):
 local=g*(N.derivative(i)*den-N*den.derivative(i))-fi*(N.derivative(0)*den-N*den.derivative(0));R+=local;print('tangent',i,'terms',len(local),'elapsed',round(time.time()-st,1),flush=True)
q=1+2*b-u;r=c*c+2*c*d-z*u;hn=q*q*r+2*q*r*r;P=(1-u)*(c*c-z*u);A=hn*P;W=-(A.derivative(0)*g-A*g.derivative(0));tn=2*b*d*(u*(W.derivative(0)*g-2*W*g.derivative(0))-2*W*g);td=63*ell**2*u**5*g**3
raw=R*td-g*den**2*tn;print('cleared terms',len(raw),'elapsed',round(time.time()-st,1),flush=True)
quo,rem=divmod(raw,F0);assert rem.is_zero() and raw==quo*F0;print('PASS exact complete mixed current by independent common denominator FLINT',round(time.time()-st,1),'quotient terms',len(quo),flush=True)
