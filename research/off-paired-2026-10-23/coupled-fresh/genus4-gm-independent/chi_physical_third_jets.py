"""Complete χ compact first/second/third physical jets and kernel relations.

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

# Literal universal third root derivatives depend only on the product of
# coefficient monomials and its b-exponent at fixed q, a=q^3/b.
exps=(-2,2,0,-1,0,0)
H1=-4*r.A*g.ap**2-r.D*g.ap*g.qp-4*r.B*g.bp**2
K1=8*r.A*g.ap**2+r.D*g.ap*g.qp-8*r.B*g.bp**2
UU=g.J-H1
VV=3*H1-K1-2*g.J

def rat(n,d=1):return n*r.inv(d)%p
ld={(1,1):rat(1,2*r.B*r.B),(5,5):rat(-1,2*r.T*r.T)}
ldd={(1,1,1):rat(-1,r.B**3),(5,5,5):rat(1,r.T**3)}
def f2(i,j):return (lp[i]*lp[j]-ld.get((i,j),0))%p
def f3(i,j,k):
 return (-lp[i]*lp[j]*lp[k]+ld.get((i,j),0)*lp[k]
         +ld.get((i,k),0)*lp[j]+ld.get((j,k),0)*lp[i]-ldd.get((i,j,k),0))%p
third={}
for i in range(6):
 for j in range(i,6):
  for k in range(j,6):
   ids=(i,j,k);N=sum(exps[v]for v in ids)
   prod=mp[i]*mp[j]*mp[k]
   v=g.bp*prod*(N*(N-1)*g.J**2+(3*N*UU+VV)*g.J+3*UU**2)
   for h in range(3):
    x,y=[ids[t]for t in range(3)if t!=h]
    v-=lp[ids[h]]*g.bp*mp[x]*mp[y]*((exps[x]+exps[y])*g.J+UU)*g.J**2
   for h in range(3):
    x,y=[ids[t]for t in range(3)if t!=h]
    v+=f2(x,y)*g.bp*mp[ids[h]]*g.J**4
   v+=f3(i,j,k)*g.bp*g.J**5
   third[ids]=v*g.qp**4
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

acc3={
 (0,0,0):[0,0,rat(55,648),rat(55,432),0,0],
 (0,0,1):[0,0,rat(-5,648),rat(-5,432),0,0],
 (0,0,2):[0,0,0,rat(-5,72),0,0],
 (0,1,1):[0,0,rat(-5,648),rat(-5,432),0,0],
 (0,1,2):[0,0,0,rat(1,72),0,0],
 (0,2,2):[0,0,0,0,0,0],
 (1,1,1):[0,0,rat(55,648),rat(55,432),0,0],
 (1,1,2):[0,0,0,rat(-5,72),0,0],
 (1,2,2):[0,0,0,0,0,0],
 (2,2,2):[0,0,0,0,0,120]}
for i,j,k in acc3:
 t=g.cpoly(0)
 for c,v in zip(acc3[i,j,k],first):t+=c*v
 for ii,jj,kk in ((i,j,k),(i,k,j),(j,k,i)):
  accij=acc[min(ii,jj),max(ii,jj)]
  for x in range(6):
   for y in range(6):t+=accij[x]*V[kk][y]*second[min(x,y),max(x,y)]
 for x in range(6):
  for y in range(6):
   for z in range(6):t+=V[i][x]*V[j][y]*V[k][z]*third[tuple(sorted((x,y,z)))]
 targets.append(g.rem(t));labels.append(''.join(('R','S','z')[v]for v in (i,j,k)))

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
_,cpiv=r.rref(M,len(targets))
ker,kpiv=r.kernel(M,len(targets))
assert all(sum(row[j]*v[j]for j in range(len(targets)))%p==0 for row in M for v in ker)
pivotdet=r.det([[row[j]for j in cpiv]for row in M])
annihilator_primitives=[[sum(v[j]*exact[j][i]for j in range(len(targets)))%p for i in range(43)]for v in ker]
out={
 'prime':p,'specialization':r.out['specialization'],
 'physical_point':{'R':1,'S':1,'z':1,'k':1},
 'meaning':'columns are compact coordinates of b0 times literal physical χ derivatives, q fixed, b0²=-T/B',
 'derivative_labels':labels,'compact_columns':compact,
 'compact_rank':len(cpiv),'compact_pivot_derivative_indices':cpiv,
 'compact_pivot_determinant':pivotdet,
 'all_kernel_rows':ker,
 'annihilator_exact_primitive_coefficients':annihilator_primitives,
 'exact_function_coefficients':exact,
 'exact_function_monomials':[mon[c]for c in qc],
 'exact_function_numerator_rows':funcs,
 'exact_function_denominator':'J_h^3*q_h^4',
 'intrinsic_primitive_space_dimension':43,'compact_plus_exact_rank':50,
 'cleared_identity_checks':len(targets),
 'status':'actual complete physical first/second/third χ jets at one point; all eight compact rows retained; rational lift and actual adjoint source match not claimed',
}
(HERE/'chi-physical-third-jets-results.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps({k:out[k]for k in ('prime','derivative_labels','compact_rank','compact_pivot_derivative_indices','compact_plus_exact_rank','cleared_identity_checks','status')},indent=2))
