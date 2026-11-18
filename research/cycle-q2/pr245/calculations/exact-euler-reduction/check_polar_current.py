"""Full rank-160 replay of the two-direction Δ_D leading-pole current at (3,7)."""
from fractions import Fraction as F
from pathlib import Path
from flint import fmpq, fmpq_mat
import argparse,json
from rational_cyclic_oracle import macaulay,monomials,product,plus
p=argparse.ArgumentParser();p.add_argument('source_json');p.add_argument('connection_log');a=p.parse_args()
src=json.loads(Path(a.source_json).read_text()); D=json.loads(Path(a.connection_log).read_text().splitlines()[-1])
I=fmpq(src['I']);J=fmpq(src['J'])
m8,h8,r8=macaulay(8,I,J);m14,_,r14=macaulay(14,I,J)
C=[]
for e,s in [((1,1,2),fmpq(-1,2)),((0,0,3),fmpq(-1))]:
    l=product(monomials(2),m8,e);h=product(h8,m14,e)
    C.append(plus(r8[0]*l,r8[0]*r14[0]*h)*s)
ai,aj=C
# M=e_tau tensor ψ_(6,2). Nine selected indices 0,1,2,3,4,5,7,8,9.
ei,psi=3,15
co=[fmpq(x) for x in src['source_coordinates']]
n=[]
for i in range(8):
 for k in range(20):
  M=int(i==ei and k==psi)
  MI=ai[i,ei]*int(k==psi)+int(i==ei)*fmpq(D['A_I'][k][psi])
  MJ=aj[i,ei]*int(k==psi)+int(i==ei)*fmpq(D['A_J'][k][psi])
  # Target minus current divided by I^4 in the original (I,J) frame.
  w=-int(i==ei)*co[k]/(24*I**3)
  rem=w+fmpq(M,8)+I*MI/36+J*MJ/24
  if rem:n.append((i,k,str(rem)))
print('nonzero residual coordinates over Q:',len(n),'of 160')
print('first surviving coordinate (C basis index,D basis index,rational value):',n[0] if n else None)
print('non-e_tau coordinates:',[(i,k,v) for i,k,v in n if i!=ei])
