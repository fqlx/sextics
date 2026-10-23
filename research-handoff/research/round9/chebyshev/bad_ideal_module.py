from pathlib import Path
import pickle,sympy as S,json
P=Path(__file__).parent;d=pickle.loads((P/'normalized_algebra.pickle').read_bytes());q,h=d['q'],d['h'];sig=54*(1+q**6)**2*h-q**3;nw=[(0,0),(4,2),(8,5),(12,6),(8,3),(16,3)];bad=[]
for i,M in enumerate(d['matrices'][1:],1):
 for j in range(6):
  z=S.Poly(M[0,j],q,h);r=S.rem(z,S.Poly(sig,q,h)).as_expr()
  if r!=0:bad.append((i,j,str(r)))
assert not bad
# Kernel of N=O(2Dinf)→O_S is free with columnsS*e0,e1,...e5.
D=S.diag(sig,1,1,1,1,1);kw=[(12,1)]+nw[1:];viol=[]
for i,M in enumerate(d['matrices']):
 C=(D.inv()*M*D).applyfunc(S.cancel)
 for j in range(6):
  for k in range(6):
   if S.Poly(S.denom(C[k,j]),q,h).total_degree()>0:viol.append(('den',i,j,k))
   z=S.Poly(C[k,j],q,h)
   if z.is_zero:continue
   bound=[d['weights'][i][a]+kw[j][a]-kw[k][a]for a in(0,1)]
   if z.degree(q)>bound[0]or z.degree(h)>bound[1]:viol.append(('weight',i,j,k,(z.degree(q),z.degree(h)),bound))
assert not viol
out={'S':str(sig),'evaluation':'e0→1, allnonconstant e_i→0 on S','action_check':'Every constant coefficient of nonconstant algebra multiplication is divisible by S; kernel action is exact.','kernel_weights':kw,'Lmin_inverse_pushforward_weights':[(-a-2,-b-2)for a,b in kw],'full_canonical_pushforward_budgets':kw,'module_violations':viol,'geometric_scope':'Kernel equals divisorial I_Dbad⊗O(2Dinf), since it is CM/reflexive and agrees in codim1. Minimality at isolated resolution valuations still separate.','extra_canonical_generator':'dual_e0/S, global budget(q,h)=(12,1), in addition to unchanged nonconstant duals.'}
(P/'bad_ideal_module.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
