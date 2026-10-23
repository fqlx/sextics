"""Exact blocked Gaussian elimination over F_p using bounded integer float BLAS.

Input values are integers <p; panel_size*(p-1)^2 must stay <2^53.
Every BLAS multiply therefore sums exactly representable integer products.
"""
import numpy as np,time

def solve_mod(mat,rhs,p,panel_size=48,progress=False):
 assert panel_size*(p-1)**2<2**53
 assert np.issubdtype(mat.dtype,np.integer) and np.issubdtype(rhs.dtype,np.integer)
 assert np.all((mat>=0)&(mat<p)) and np.all((rhs>=0)&(rhs<p))
 assert mat.shape[1]*(p-1)**2<2**63
 A=np.column_stack((mat,rhs)).astype(np.float64);m,n=mat.shape;row=0;piv=[];start=time.monotonic()
 for begin in range(0,n,panel_size):
  end=min(n,begin+panel_size);L=np.zeros((m,panel_size),dtype=np.float64);blockrows=[];j=0
  for col in range(begin,end):
   if row==m:break
   ids=np.flatnonzero(A[row:,col])
   if not len(ids):continue
   q=row+int(ids[0])
   if q!=row:A[[row,q]]=A[[q,row]];L[[row,q]]=L[[q,row]]
   if j:
    A[row,end:]=(A[row,end:]-L[row,:j]@A[blockrows,end:])%p
   inv=pow(int(A[row,col]),-1,p)
   A[row,col:]=(A[row,col:]*inv)%p
   if row+1<m:
    factor=A[row+1:,col].copy();L[row+1:,j]=factor
    A[row+1:,col:end]=(A[row+1:,col:end]-factor[:,None]*A[row,col:end])%p
   blockrows.append(row);piv.append(col);j+=1;row+=1
  if j and row<m and end<A.shape[1]:
   # Chunking bounds allocations; each dot remains an exact integer sum.
   for a in range(row,m,512):
    b=min(m,a+512)
    A[a:b,end:]=(A[a:b,end:]-L[a:b,:j]@A[blockrows,end:])%p
  if progress and ((begin//panel_size)%4==0 or end==n):print({'columns_processed':end,'rank':len(piv),'seconds':round(time.monotonic()-start,2)},flush=True)
  if row==m:break
 bad=np.all(A[:,:n]==0,axis=1)&(A[:,n]!=0)
 if np.any(bad):return len(piv),None
 sol=np.zeros(n,dtype=np.int64)
 for r,c in reversed(list(enumerate(piv))):
  # Integer dot avoids any floating accumulation assumption outside panel bound.
  z=int(A[r,c+1:n].astype(np.int64)@sol[c+1:])%p
  sol[c]=(int(A[r,n])-z)%p
 assert np.all((mat@sol-rhs)%p==0)
 return len(piv),sol

def self_check():
 import sys
 from pathlib import Path
 sys.path.insert(0,str(Path(__file__).parents[1]))
 from two_pole_infinity_current_search import solve_mod as reference
 rng=np.random.default_rng(817253);p=1009
 for m,n in [(3,8),(8,3),(20,12),(12,20),(85,70),(70,85),(140,120)]:
  mat=rng.integers(0,p,size=(m,n),dtype=np.int64)
  if n>5:mat[:,3]=mat[:,1];mat[:,5]=0
  for consistent in [False,True]:
   rhs=mat@rng.integers(0,p,size=n,dtype=np.int64)%p if consistent else rng.integers(0,p,size=m,dtype=np.int64)
   r0,s0=reference(mat,rhs,p);r1,s1=solve_mod(mat,rhs,p,panel_size=17)
   assert r0==r1 and(s0 is None)==(s1 is None),(m,n,consistent,r0,r1)
 print('Blocked modular solver passed14 independentreference comparisons',flush=True)
if __name__=='__main__':self_check()
