"""All six genus-four compact Gauss--Manin matrices, exact mod 1009.

Uses the complete RR basis and pole-divisor spaces, not a degree ansatz.
Every rational identity is verified after clearing its literal denominator
q^5 J^3 and reducing by the actual complete-intersection ideal.
"""
import importlib.util
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('rr',HERE/'construct_rr_basis.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
p=r.p

def mm(a,b):
 return [[sum(x*y for x,y in zip(row,col))%p for col in zip(*b)]for row in a]
def inverse(a):
 n=len(a);rr,piv=r.rref([row+[int(i==j)for j in range(n)]for i,row in enumerate(a)],n)
 assert len(piv)==n
 return [row[n:]for row in rr]

M=r.conditions
Minv=inverse([[row[c]for c in r.jpiv]for row in M])
Bb=[list(row)for row in zip(*r.basis)] # 33 x 8

def monomial_variation(exps,vals,dvals):
 out=r.zero
 for j,n in enumerate(exps):
  if not n:continue
  term=r.scale(dvals[j],n)
  for k,(m,val) in enumerate(zip(exps,vals)):
   term=r.mul(term,r.power(val,m-int(j==k)))
  out=r.add(out,term)
 return out

def branch_parameter_variation(kind,vals,theta):
 a,b,q,t=vals
 monoms=[r.mul(a,a),r.mul(b,b),r.mul(q,q),r.mul(a,q),r.mul(q,t),r.mul(t,t)]
 v=monoms[theta]
 if kind in ('a','b'):
  J=r.add(r.add(r.scale(r.mul(a,a),2*r.A),r.scale(r.mul(a,q),r.D)),r.scale(r.mul(b,b),-2*r.B))
  w=r.mul(v,r.recip(J))
  return [r.neg(r.mul(a,w)),r.mul(b,w),r.zero,r.zero]
 Qb=r.scale(b,2*r.B)
 Qt=r.add(r.scale(q,r.E),r.scale(t,2*r.T))
 den=r.add(r.mul(b,Qb),r.neg(r.mul(t,Qt)))
 w=r.mul(v,r.recip(den))
 return [r.zero,r.neg(r.mul(b,w)),r.zero,r.mul(t,w)]

def basis_derivative(theta):
 blocks=[]
 for (kind,root),vals in zip(r.labels[1:],r.branches[1:]):
  dv=branch_parameter_variation(kind,vals,theta)
  jets=[monomial_variation(r.mon6[c],vals,dv)for c in r.quotcols]
  blocks.extend([[v[n]for v in jets]for n in range(5)])
 rhs=mm(blocks,Bb)
 sol=mm(Minv,rhs)
 out=[[0]*8 for _ in range(33)]
 for c,row in zip(r.jpiv,sol):out[c]=[-x%p for x in row]
 # Full differentiated-kernel identity, including nonpivot columns.
 left=mm(M,out)
 assert all((left[i][j]+rhs[i][j])%p==0 for i in range(25)for j in range(8))
 return [list(row)for row in zip(*out)]

Fconds=[[r.jets[j][col][n]for col in range(33)]for j in range(1,6)for n in range(4)]
Fbasis,Fpiv=r.kernel(Fconds,33)
assert len(Fbasis)==13 and len(Fpiv)==20

a,b,q=s.symbols('a b q')
vars=(a,b,q)
def poly(expr):return s.Poly(expr,*vars,modulus=p)
def cpoly(n):return poly(int(n)%p)
ap,bp,qp=map(poly,vars)
Q=poly(r.A*a*a+r.B*b*b+r.C*q*q+r.D*a*q+r.E*q+r.T)
C1=poly(a*b-q**3)
J=poly(2*r.A*a*a+r.D*a*q-2*r.B*b*b)
Qa=Q.diff(a);Qb=Q.diff(b);Qq=Q.diff(q)
aq=-ap*Qq-3*qp**2*Qb
bq=bp*Qq+3*qp**2*Qa
Jqnum=J*J.diff(q)+J.diff(a)*aq+J.diff(b)*bq
monomials=[poly(a**r.mon6[c][0]*b**r.mon6[c][1]*q**r.mon6[c][2])for c in r.quotcols]
def lincomb(row):
 out=cpoly(0)
 for coef,m in zip(row,monomials):
  if coef:out+=int(coef)*m
 return out
Nbasis=[lincomb(v)for v in r.basis]
Hbasis=[lincomb(v)for v in Fbasis]
beta_columns=[v*J**2 for v in Nbasis]
df_columns=[]
for h in Hbasis:
 hqnum=J*h.diff(q)+h.diff(a)*aq+h.diff(b)*bq
 df_columns.append(qp*J*hqnum-qp*h*Jqnum-4*h*J**2)

print('Constructing exact affine Groebner reduction',flush=True)
G=s.groebner([Q.as_expr(),C1.as_expr()],a,b,q,modulus=p,order='grevlex')
def rem(v):return poly(G.reduce(v.as_expr())[1])
columns=[rem(v)for v in beta_columns+df_columns]
column_words=sorted(set(m for v in columns for m,c in v.terms()))
column_matrix=[[v.coeff_monomial(m)%p for v in columns]for m in column_words]
_,independent=r.rref(column_matrix,len(columns))
assert len(independent)==20 and set(range(8))<=set(independent)
assert len([j for j in independent if j>=8])==12
chosen=[columns[j]for j in independent]

parameter_monomials=[ap**2,bp**2,qp**2,ap*qp,qp,cpoly(1)]
Jexplicit=[2*ap**2,-2*bp**2,cpoly(0),ap*qp,cpoly(0),cpoly(0)]
targets=[];target_labels=[]
for theta in range(6):
 derivatives=basis_derivative(theta)
 for j,(n,drow) in enumerate(zip(Nbasis,derivatives)):
  dn=lincomb(drow)
  tor=-ap*n.diff(a)+bp*n.diff(b)
  jtor=-ap*J.diff(a)+bp*J.diff(b)
  target=dn*J**2+parameter_monomials[theta]*tor*J-n*Jexplicit[theta]*J-n*parameter_monomials[theta]*jtor
  targets.append(rem(target));target_labels.append(('ABCDE T'.replace(' ', '')[theta],j))

words=sorted(set(m for v in chosen+targets for m,c in v.terms()))
matrix=[[v.coeff_monomial(m)%p for v in chosen+targets]for m in words]
rr,piv=r.rref(matrix,20)
assert len(piv)==20
# rref only keeps pivot rows; independently verify every cleared identity.
coefficients=[[rr[i][20+j]for i in range(20)]for j in range(48)]
checks=0
for target,coefs in zip(targets,coefficients):
 error=target
 for c,col in zip(coefs,chosen):error-=c*col
 assert error.is_zero
 checks+=1

matrices={}
primitive_coefficients={}
for k,label in enumerate('ABCDET'):
 cols=[];prims=[]
 for j in range(8):
  co=coefficients[8*k+j]
  full=[0]*21
  for c,col in zip(co,independent):full[col]=c
  cols.append(full[:8]);prims.append(full[8:])
 matrices[label]={'columns':cols}
 primitive_coefficients[label]={'columns':prims}

out={
 'prime':p,'specialization':r.out['specialization'],
 'field_extensions':r.out['chart_points'],
 'RR_basis_dimension':8,'primitive_function_dimension_including_constants':13,
 'combined_reduction_rank':len(independent),'independent_column_indices':independent,
 'cleared_identity_checks':checks,
 'connection':matrices,'exact_primitive_coefficients':primitive_coefficients,
 'primitive_function_numerator_rows':Fbasis,
 'literal_exact_primitive':'sum row[i]*degree6_monomial[i]/(J*q^4)',
 'basis_convention':'columns; dtheta beta_j=sum_i Mtheta[i,j] beta_i+dq(exact primitive)',
 'status':'all six complete compact GM matrices at one actual coefficient point, with 48 exact ideal identities; universal determinant construction retained separately; no primitive claimed',
}
(HERE/'gm-at-point-results.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps({k:out[k]for k in ('prime','RR_basis_dimension','primitive_function_dimension_including_constants','combined_reduction_rank','cleared_identity_checks','status')},indent=2))
