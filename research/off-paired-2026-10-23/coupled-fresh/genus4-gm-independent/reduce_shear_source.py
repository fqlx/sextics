"""Actual all-eight-component q*eta_b reduction with infinity retained."""
import importlib.util,json
from pathlib import Path
HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('gm',HERE/'compute_gm_at_point.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
r=g.r;p=r.p

mon5=r.exponents(5);ix={m:i for i,m in enumerate(mon5)}
relations=[]
for form,degree in ((r.Q,3),(r.C1,2)):
 for m in r.exponents(degree):
  row=[0]*len(mon5)
  for n,c in form.items():row[ix[tuple(x+y for x,y in zip(m,n))]]=c%p
  relations.append(row)
_,piv=r.rref(relations,len(mon5))
cols=[i for i in range(len(mon5))if i not in piv]
assert len(cols)==27
jets=[[r.evmon(mon5[c],vals)for c in cols]for vals in r.branches]
# Denominator q_h^4 t_h: finite nonmarked branches require 4 zeros;
# infinity q_h has order1,t_h order3, so 6 zeros leave only a simple pole.
conditions=[[jets[j][i][n]for i in range(27)]for j in range(1,6)for n in range(4 if j<4 else 6)]
functions,fpiv=r.kernel(conditions,27)
assert len(fpiv)==24 and len(functions)==3

mons=[g.poly(g.a**mon5[c][0]*g.b**mon5[c][1]*g.q**mon5[c][2])for c in cols]
def lc(row):
 ans=g.cpoly(0)
 for c,m in zip(row,mons):
  if c:ans+=int(c)*m
 return ans
hs=[lc(row)for row in functions]
dfs=[]
for h in hs:
 dfs.append(g.rem(g.qp*(g.J*h.diff(g.q)+h.diff(g.a)*g.aq+h.diff(g.b)*g.bq)-4*h*g.J))
columns=[g.rem(n)for n in g.Nbasis]+dfs
targets=[g.rem(g.qp**6*g.bp),g.rem(g.qp**5*g.bp)]
words=sorted(set(m for v in columns+targets for m,c in v.terms()))
matrix=[[v.coeff_monomial(m)%p for v in columns+targets]for m in words]
_,ind=r.rref(matrix,11)
assert len(ind)==10 and set(range(8))<=set(ind)
chosen=[columns[c]for c in ind]
matrix=[[v.coeff_monomial(m)%p for v in chosen+targets]for m in words]
rr,pv=r.rref(matrix,10)
assert len(pv)==10
answers=[]
for j,target in enumerate(targets):
 co=[rr[i][10+j]for i in range(10)]
 error=target
 for c,col in zip(co,chosen):error-=c*col
 assert error.is_zero
 full=[0]*11
 for c,col in zip(co,ind):full[col]=int(c)%p
 answers.append({'compact_coefficients':full[:8],'exact_function_coefficients':full[8:]})

out={
 'prime':p,'specialization':r.out['specialization'],
 'RR_compact_basis_dimension':8,
 'simple_infinity_primitive_space_dimension':3,
 'combined_reduction_rank':10,
 'q_eta_b':answers[0],'eta_b':answers[1],
 'exact_function_numerator_rows':functions,
 'exact_function_monomials':[mon5[c]for c in cols],
 'exact_function_denominator':'q_h^4*t_h (homogeneous), equivalently q_aff^4 on affine t=1',
 'literal_identities':'q*eta_b=sum compact[i]*beta_i + d_q(sum exact[i]*f_i), same for eta_b',
 'checks':2,
 'status':'complete rank8 source reduction with actual simple infinity primitives; no infinity class discarded and no primitive claimed',
}
(HERE/'shear-source-reduction-results.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps({k:out[k]for k in ('prime','RR_compact_basis_dimension','simple_infinity_primitive_space_dimension','combined_reduction_rank','q_eta_b','checks','status')},indent=2))
