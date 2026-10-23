#!/usr/bin/env python3
"""Independent standard-library audit of five relative-threefold obstructions.
Computes exact finite-field ranks and a characteristic-zero rank sandwich.
No CAS, numerical rank, or claimed finite-field-to-Q inference without a bound.
"""
from fractions import Fraction as F
from itertools import combinations, product, permutations
from functools import reduce
from math import gcd
import json, time
from pathlib import Path
P=101
NAMES=('c','d','s','P','U')
# Physical torus variables (x,y,z,a,b)=(X1,Y0,Y1,X2,Y2)/X0.
E=((1,-2,0,0,0),(0,-3,1,0,0),(0,6,0,0,0),(0,3,0,1,1),(0,0,0,6,0))
SOURCE=(1,1,1,1,0)
G={(0,0,0,0,0):F(1),(0,0,1,0,0):F(1),(6,0,2,0,0):F(1),(0,6,3,0,0):F(1),(1,1,1,0,0):F(1,2),(1,0,0,1,0):F(1,3),(3,1,1,1,0):F(1,2),(0,0,0,0,1):F(1),(0,0,-3,6,-1):F(1)}
PHYSICAL={(0,0,0,0,0):F(1),(6,0,0,0,0):F(1),(0,6,0,0,0):F(1),(0,0,6,0,0):F(1),(0,0,0,6,0):F(1),(0,0,0,0,6):F(1),(1,1,1,0,0):F(1,2),(3,0,1,1,1):F(1,2),(1,1,0,1,1):F(1,3)}
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def det(A):
 return sum((-1)**sum(p[i]>p[j]for i in range(len(p))for j in range(i+1,len(p)))*reduce(lambda a,b:a*b,(A[i][p[i]]for i in range(len(p))),1)for p in permutations(range(len(A))))
def pull(e):return tuple(sum(e[j]*E[j][i]for j in range(5))for i in range(5))
assert {pull(e):c for e,c in G.items()}==PHYSICAL
assert abs(det(E))==36
assert pull(SOURCE)==(1,4,1,1,1) # y^3 dx dy dz da db in logarithmic coordinates.
# Exact coefficient loads in the homogeneous six-variable physical polynomial.
loads=[F(0)]*6
for e,c in PHYSICAL.items():
 if c==1:continue
 eh=(6-sum(e),)+e
 for i,v in enumerate(eh):loads[i]+=abs(c)*v
assert all(v<6 for v in loads)
print('PASS: target substitution, source Jacobian, quotient degree 36, and all face AM-GM bounds.',flush=True)
def facets(points):
 out=set()
 for aa in combinations(points,4):
  mat=[tuple(x-y for x,y in zip(a,aa[0]))for a in aa[1:]]
  n=tuple((-1)**j*det([r[:j]+r[j+1:]for r in mat])for j in range(4))
  if not any(n):continue
  h=dot(n,aa[0]);s=[dot(n,x)-h for x in points]
  if max(s)<=0:pass
  elif min(s)>=0:n=tuple(-x for x in n);h=-h
  else:continue
  d=reduce(gcd,map(abs,n+(h,)));out.add(tuple(x//d for x in n)+(h//d,))
 return sorted(out)
def lattice(points,fac,k,interior=False):
 box=[range(k*min(x[i]for x in points),k*max(x[i]for x in points)+1)for i in range(4)]
 return [v for v in product(*box)if all(dot(f[:4],v)<k*f[4]if interior else dot(f[:4],v)<=k*f[4]for f in fac)]
def mod(q):return q.numerator*pow(q.denominator,-1,P)%P
def addexp(a,b):return tuple(x+y for x,y in zip(a,b))
def shifted(g,e,rows,offset=0,sign=1):return {offset+rows[addexp(a,e)]:sign*c%P for a,c in g.items()if c%P}
def rank(columns):
 piv={}
 for original in columns:
  col={i:c%P for i,c in original.items()if c%P}
  while col:
   row=min(col);v=col[row]
   if row not in piv:
    inv=pow(v,-1,P);piv[row]={i:c*inv%P for i,c in col.items()};break
   for i,c in piv[row].items():
    x=(col.get(i,0)-v*c)%P
    if x:col[i]=x
    else:col.pop(i,None)
 return len(piv)
REPORT=[]
for base in range(5):
 tic=time.time();active=tuple(i for i in range(5)if i!=base)
 project=lambda e:tuple(e[i]for i in active)
 points=sorted(set(project(e)for e in G));fac=facets(points)
 assert len(fac)>=5
 L1,L2,L3,L4=[lattice(points,fac,k)for k in range(1,5)]
 interior=lattice(points,fac,1,True);b=project(SOURCE)
 assert all(dot(f[:4],b)<2*f[4]for f in fac)
 row3={e:i for i,e in enumerate(L3)};row4={e:i for i,e in enumerate(L4)}
 g={};dg={}
 for e,c in G.items():
  value=mod(c*F(2)**e[base]);a=project(e)
  g[a]=(g.get(a,0)+value)%P;dg[a]=(dg.get(a,0)+e[base]*value)%P
 gens=[g]+[{e:c*e[i]%P for e,c in g.items()}for i in range(4)]
 M=[shifted(g,e,row4)for g in gens for e in L3]
 K=[]
 for i,j in combinations(range(5),2):
  for e in L2:
   col=shifted(gens[j],e,row3,i*len(L3))
   col.update(shifted(gens[i],e,row3,j*len(L3),-1));K.append(col)
 for k in K:
  out={}
  for j,a in k.items():
   for i,c in M[j].items():out[i]=(out.get(i,0)+a*c)%P
  assert not any(out.values())
 print(NAMES[base],'matrices constructed',flush=True)
 kr=rank(K);mr=rank(M);upper=len(M)-kr
 assert mr==upper
 dg2={}
 for a,c in dg.items():
  for e,d in dg.items():
   z=addexp(a,e);dg2[z]=(dg2.get(z,0)+c*d)%P
 t=shifted(dg2,b,row4);ar=rank(M+[t]);assert ar==mr+1
 result={'base':NAMES[base],'active':[NAMES[i]for i in active],'specialization':2,'prime':P,'lattice_counts':list(map(len,[L1,L2,L3,L4])),'interior_count':len(interior),'J0_shape':[len(L4),len(M)],'K_shape':[len(M),len(K)],'K_rank':kr,'J0_rank':mr,'generic_rank_upper_bound':upper,'second_derivative_augmented_rank':ar}
 REPORT.append(result)
 print('PASS:',NAMES[base],'K rank',kr,'M rank/bound',mr,'second variation augmented',ar,'seconds',round(time.time()-tic,2),flush=True)
 Path(__file__).with_name('coordinate_threefold_audit.json').write_text(json.dumps(REPORT,indent=2)+'\n')
print('PASS: all five characteristic-zero generic second-variation nonmembership obstructions.',flush=True)
print('Scope: relative threefold primitives; all five quotient coordinate directions are necessary.',flush=True)
print('The unrestricted physical certificate problem remains open.',flush=True)
