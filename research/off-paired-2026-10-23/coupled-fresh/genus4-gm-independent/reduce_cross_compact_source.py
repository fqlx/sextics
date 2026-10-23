"""Actual full-eight-component cross compact source, infinity retained."""
import importlib.util,json
from pathlib import Path
HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('gm',HERE/'compute_gm_at_point.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
r=g.r;p=r.p

mon5=r.exponents(4);ix={m:i for i,m in enumerate(mon5)}
relations=[]
for form,degree in ((r.Q,2),(r.C1,1)):
 for m in r.exponents(degree):
  row=[0]*len(mon5)
  for n,c in form.items():row[ix[tuple(x+y for x,y in zip(m,n))]]=c%p
  relations.append(row)
_,piv=r.rref(relations,len(mon5))
cols=[i for i in range(len(mon5))if i not in piv]
assert len(cols)==21
jets=[[r.evmon(mon5[c],vals)for c in cols]for vals in r.branches]
# Denominator q_h^4: cancel other three affine q-zero branches, and
# retain all four allowed pole orders at BOTH infinity points.
conditions=[[jets[j][i][n]for i in range(21)]for j in range(1,4)for n in range(4)]
functions,fpiv=r.kernel(conditions,21)
assert len(fpiv)==12 and len(functions)==9

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
Cp=(r.C-r.D*r.D*r.inv(4*r.A))%p
cross_r=(Cp-r.E*r.E*r.inv(4*r.T))*r.inv(2*r.T)%p
N=(r.inv(2)*g.aq+(2*r.D*g.ap+r.E)*g.qp*g.aq*r.inv(4*r.T)
   -(r.D*g.ap**2+r.E*g.ap)*g.J*r.inv(4*r.T)-cross_r*g.ap*g.qp*g.J)
ss=r.D*Cp*r.inv(2*r.A)%p
N+=cross_r*ss*g.qp**4 # REQUIRED infinity-residue correction, never dropped.
targets=[g.rem(g.qp**3*N)]
words=sorted(set(m for v in columns+targets for m,c in v.terms()))
matrix=[[v.coeff_monomial(m)%p for v in columns+targets]for m in words]
_,ind=r.rref(matrix,17)
assert len(ind)==16 and set(range(8))<=set(ind)
chosen=[columns[c]for c in ind]
matrix=[[v.coeff_monomial(m)%p for v in chosen+targets]for m in words]
rr,pv=r.rref(matrix,16)
assert len(pv)==16
answers=[]
for j,target in enumerate(targets):
 co=[rr[i][16+j]for i in range(16)]
 error=target
 for c,col in zip(co,chosen):error-=c*col
 assert error.is_zero
 full=[0]*17
 for c,col in zip(co,ind):full[col]=int(c)%p
 answers.append({'compact_coefficients':full[:8],'exact_function_coefficients':full[8:]})

out={
 'prime':p,'specialization':r.out['specialization'],
 'RR_compact_basis_dimension':8,
 'order4_infinity_primitive_space_dimension':9,
 'combined_reduction_rank':16,
 'psi_hat_b':answers[0],
 'exact_function_numerator_rows':functions,
 'exact_function_monomials':[mon5[c]for c in cols],
 'exact_function_denominator':'q_h^4 (homogeneous), equivalently q_aff^4 on affine t=1',
 'literal_identities':'psi_hat_b=xi2+dF_b-r*xi+r*s*q^2dq/J=sum compact[i]*beta_i+d_q(sum exact[i]*f_i)',
 'infinity_companion':{'r':int(cross_r),'s':int(ss),'required_correction':'r*s*q^2dq/J'},
 'checks':1,
 'status':'actual full compact cross-source reduction retaining infinity orders up to5 and exact primitives up to4; no primitive claimed',
}
(HERE/'cross-compact-source-reduction-results.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps({k:out[k]for k in ('prime','RR_compact_basis_dimension','order4_infinity_primitive_space_dimension','combined_reduction_rank','psi_hat_b','checks','status')},indent=2))
