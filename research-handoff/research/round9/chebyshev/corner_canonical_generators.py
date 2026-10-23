from pathlib import Path
import pickle,sympy as S,json
P=Path(__file__).parent;d=pickle.loads((P/'normalized_algebra.pickle').read_bytes());q,h=d['q'],d['h'];weights=d['weights'];MM=[]
for i,M in enumerate(d['matrices']):
 B=S.zeros(6)
 for j in range(6):
  for k in range(6):
   z=S.Poly(M[k,j],q);bound=weights[i][0]+weights[j][0]-weights[k][0]
   if bound>=0:B[k,j]=z.nth(bound).subs(h,0)
 MM.append(B)
span=S.Matrix.hstack(*[m.T for m in MM[1:]]);rank=span.rank();E=S.eye(6);gen=[]
for i in range(6):
 if S.Matrix.hstack(span,E[:,i]).rank()>rank:gen.append(i)
assert S.Matrix.hstack(span,E[:,0]).rank()==rank
# All nonconstant dual basis elements extend to global omega_S tensor L0(-2Dinf): multiply q-homog coeff and h0²; h budget >=2.
assert all(weights[i][1]>=2 and weights[i][0]>=2 for i in range(1,6))
out={'fiber_multiplication':[str(x)for x in MM],'fiber_socle_dimension':6-rank,'dual_basis_nonzero_mod_momega':gen,'dual_e0_in_momega':True,'available_global_duals':list(range(1,6)),'available_Q_jets_per_dual':[weights[i][0]for i in range(1,6)],'scope':'Exact Nakayama generation of local canonical module at corner by restrictions of global sections. Does not by itself prove jet surjectivity to the finite adjoint defect.'}
(P/'corner_canonical_generators.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='fiber_multiplication'},indent=2))
