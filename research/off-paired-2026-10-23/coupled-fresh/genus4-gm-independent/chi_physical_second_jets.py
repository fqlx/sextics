"""Complete χ compact first/second physical jets and signed-minor relation.

All pole orders are intrinsic RR orders, with 8 compact and 42 exact columns.
This is exact mod1009 at R=S=z=k=1; it is not a rational-source certificate.
"""
import importlib.util,json
from pathlib import Path
import sympy as s
HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('gm',HERE/'compute_gm_at_point.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
r=g.r;p=r.p

mon=r.exponents(10);ix={m:i for i,m in enumerate(mon)}
rels=[]
for form,degree in ((r.Q,8),(r.C1,7)):
 for m in r.exponents(degree):
  row=[0]*len(mon)
  for n,c in form.items():row[ix[tuple(x+y for x,y in zip(m,n))]]=c%p
  rels.append(row)
_,piv=r.rref(rels,len(mon));qc=[i for i in range(len(mon))if i not in piv]
assert len(qc)==57
jets=[[r.evmon(mon[c],vals)for c in qc]for vals in r.branches]
conditions=[[jets[j][i][n]for i in range(57)]for j in range(1,6)for n in range(4 if j<4 else 1)]
funcs,fpiv=r.kernel(conditions,57)
assert len(fpiv)==14 and len(funcs)==43
mons=[g.poly(g.a**mon[c][0]*g.b**mon[c][1]*g.q**mon[c][2])for c in qc]
def lc(row):
 ans=g.cpoly(0)
 for c,m in zip(row,mons):
  if c:ans+=int(c)*m
 return ans
Hs=[lc(row)for row in funcs]
columns=[g.rem(n*g.J**4)for n in g.Nbasis]
for h in Hs:
 hn=g.J*h.diff(g.q)+h.diff(g.a)*g.aq+h.diff(g.b)*g.bq
 columns.append(g.rem(g.qp*g.J*hn-3*g.qp*h*g.Jqnum-4*h*g.J**2))
print('Intrinsic 50-column compact/exact χ reduction built',flush=True)

AA,BB,CC,DD,EE,TT=s.symbols('A B C D E T')
theta=(AA,BB,CC,DD,EE,TT)
a,b,q=g.vars
Js=2*AA*a*a+DD*a*q-2*BB*b*b
ms=[a*a,b*b,q*q,a*q,q,s.Integer(1)]
logs=[s.Integer(0),-1/(2*BB),s.Integer(0),s.Integer(0),s.Integer(0),1/(2*TT)]
U=[b*(m-l*Js)for m,l in zip(ms,logs)]
sub=dict(zip(theta,(r.A,r.B,r.C,r.D,r.E,r.T)))
def pp(expr):
 expr=s.cancel(expr.subs(sub))
 den,num=s.Poly(expr,*g.vars,domain=s.QQ).clear_denoms()
 return g.poly(num.as_expr())*r.inv(int(den))
up=[pp(u)for u in U]
mp=[pp(m)for m in ms]
jexp=[pp(s.diff(Js,t))for t in theta]
lp=[int(s.numer(l.subs(sub)))*r.inv(int(s.denom(l.subs(sub))))%p for l in logs]
first=[u*g.qp**4*g.J**4 for u in up]
second={}
for i in range(6):
 for j in range(i,6):
  ue=pp(s.diff(U[i],theta[j]))
  tor=-g.ap*up[i].diff(a)+g.bp*up[i].diff(b)
  jtor=-g.ap*g.J.diff(a)+g.bp*g.J.diff(b)
  v=ue*g.J**2+mp[j]*tor*g.J-up[i]*jexp[j]*g.J-up[i]*mp[j]*jtor-lp[j]*up[i]*g.J**2
  second[i,j]=v*g.qp**4*g.J**2

def rat(n,d=1):return n*r.inv(d)%p
# Actual coefficient jets for A=1+R,B=1+S,C=k/3,D=zk/2,
# E=z/2,T=1+z^6, k^6=RS at R=S=z=k=1.
V=[[1,0,rat(1,18),rat(1,12),0,0],
   [0,1,rat(1,18),rat(1,12),0,0],
   [0,0,0,rat(1,2),rat(1,2),6]]
acc={
 (0,0):[0,0,rat(-5,108),rat(-5,72),0,0],
 (0,1):[0,0,rat(1,108),rat(1,72),0,0],
 (0,2):[0,0,0,rat(1,12),0,0],
 (1,1):[0,0,rat(-5,108),rat(-5,72),0,0],
 (1,2):[0,0,0,rat(1,12),0,0],
 (2,2):[0,0,0,0,0,30]}
targets=[];labels=[]
for i in range(3):
 t=g.cpoly(0)
 for c,v in zip(V[i],first):t+=c*v
 targets.append(g.rem(t));labels.append(('R','S','z')[i])
for i,j in acc:
 t=g.cpoly(0)
 for c,v in zip(acc[i,j],first):t+=c*v
 for k in range(6):
  for l in range(6):t+=V[i][k]*V[j][l]*second[min(k,l),max(k,l)]
 targets.append(g.rem(t));labels.append(('R','S','z')[i]+('R','S','z')[j])

words=sorted(set(m for v in columns+targets for m,c in v.terms()))
matrix=[[v.coeff_monomial(m)%p for v in columns]for m in words]
_,ind=r.rref(matrix,len(columns))
assert len(ind)==50 and set(range(8))<=set(ind)
chosen=[columns[j]for j in ind]
matrix=[[v.coeff_monomial(m)%p for v in chosen+targets]for m in words]
rr,pivs=r.rref(matrix,50);assert len(pivs)==50
compact=[];exact=[]
for j,target in enumerate(targets):
 co=[rr[i][50+j]for i in range(50)]
 err=target
 for c,col in zip(co,chosen):err-=c*col
 assert err.is_zero
 full=[0]*51
 for c,col in zip(co,ind):full[col]=int(c)%p
 compact.append(full[:8]);exact.append(full[8:])

M=[list(row)for row in zip(*compact)]
_,cpiv=r.rref(M,9)
minor=[(-1)**j*r.det([[row[k]for k in range(9)if k!=j]for row in M])%p for j in range(9)]
assert all(sum(row[j]*minor[j]for j in range(9))%p==0 for row in M)
ker,kpiv=r.kernel(M,9)
out={
 'prime':p,'specialization':r.out['specialization'],
 'physical_point':{'R':1,'S':1,'z':1,'k':1},
 'meaning':'columns are compact coordinates of b0 times literal physical χ derivatives, q fixed, b0²=-T/B',
 'derivative_labels':labels,'compact_columns':compact,
 'compact_rank':len(cpiv),'signed_minor_annihilator_coefficients':minor,
 'all_kernel_rows':ker,
 'exact_function_coefficients':exact,
 'exact_function_monomials':[mon[c]for c in qc],
 'exact_function_numerator_rows':funcs,
 'exact_function_denominator':'J_h^3*q_h^4',
 'intrinsic_primitive_space_dimension':43,'compact_plus_exact_rank':50,
 'cleared_identity_checks':9,
 'status':'actual complete physical first/second χ jet relation at one point; universal determinant mechanism exists, but rational lift and actual adjoint source match not claimed',
}
(HERE/'chi-physical-second-jets-results.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps({k:out[k]for k in ('prime','derivative_labels','compact_rank','signed_minor_annihilator_coefficients','compact_plus_exact_rank','cleared_identity_checks','status')},indent=2))
