"""Independent stdlib check of the saved exact positive rank certificate."""
import json
from pathlib import Path
P=Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/two-operator/common-factor-rank-results.json')
d=json.loads(P.read_text());p=d['prime'];M=d['universal_image_matrix_mod_p'];rows=d['coefficient_derivative_rows_mod_p']
def det(A):
 A=[r[:]for r in A];out=1
 for c in range(len(A)):
  k=next((r for r in range(c,len(A))if A[r][c]%p),None)
  if k is None:return 0
  if k!=c:A[k],A[c]=A[c],A[k];out=-out
  v=A[c][c]%p;out=out*v%p;iv=pow(v,-1,p)
  for r in range(c+1,len(A)):
   t=A[r][c]*iv%p
   for j in range(c,len(A)):A[r][j]=(A[r][j]-t*A[c][j])%p
 return out%p
idx=d['independent_derivative_indices'];cols=d['pivot_monomial_indices']
minor=[[rows[r][c]for c in cols]for r in idx]
D=det(minor);assert D
cyc=[0,1,3,6];DC=det([[M[r][c]for c in cyc]for r in range(4)]);assert DC
for row in rows:
 for m in M:assert sum(x*y for x,y in zip(row,m))%p==0
print('11x11 common-factor minor modulo',p,'=',D)
print('Universal 4x4 cyclic image minor modulo',p,'=',DC)
print('All saved rows lie in the exact four-row kernel modulo p.')
d['nonzero_11_minor_mod_p']=D;d['nonzero_4_cyclic_minor_mod_p']=DC
P.write_text(json.dumps(d,indent=2)+'\n')
