"""Verified finite-field sparse Wiedemann candidate/witness search.

This is a modular computational tool. A left witness does NOT by itself
exclude characteristic-zero solutions. A positive numerator requires exact
reconstruction and substitution. Every returned finite-field result is checked.
"""
from pathlib import Path
import argparse,ctypes,json,time
import numpy as np
from scipy.sparse import load_npz,csr_matrix
ROOT=Path(__file__).parent
PDEFAULT=1000003

def bm(seq,p):
 lib=ctypes.CDLL(str(ROOT/'wiedemann_bm.so'));f=lib.source_bm
 ptr=ctypes.POINTER(ctypes.c_uint64)
 f.argtypes=[ptr,ctypes.c_long,ctypes.c_uint64,ptr];f.restype=ctypes.c_long
 seq=np.ascontiguousarray(seq,dtype=np.uint64);out=np.zeros(len(seq)+1,dtype=np.uint64)
 n=f(seq.ctypes.data_as(ptr),len(seq),p,out.ctypes.data_as(ptr))
 co=out[:n].copy();co=(co*np.uint64(pow(int(co[-1]),-1,p)))%np.uint64(p)
 return co

def solve(M,b,p=PDEFAULT,seed=2036,outprefix=None,progress=True):
 t0=time.time();p64=np.uint64(p);M=M.tocsr().astype(np.uint64);M.sum_duplicates();M.data%=p64;M.eliminate_zeros();Mt=M.T.tocsr()
 b=np.asarray(b,dtype=np.uint64)%p64;n,m=M.shape
 rowdegrees=np.diff(M.indptr);coldegrees=np.diff(Mt.indptr)
 assert int(max(rowdegrees.max(initial=0),coldegrees.max(initial=0)))*(p-1)**2<2**64
 assert n*(p-1)**2<2**64 and np.all(M.data<p64)
 zero=np.flatnonzero(rowdegrees==0)
 if any(b[zero]):
  i=next(int(i)for i in zero if b[i]);w=np.zeros(n,dtype=np.uint64);w[i]=1
  return {'kind':'left_witness','w':w,'dot':int(b[i]),'seconds':time.time()-t0}
 rng=np.random.default_rng(seed)
 S=rng.integers(1,p,size=n,dtype=np.uint64);W=rng.integers(1,p,size=m,dtype=np.uint64);u=rng.integers(0,p,size=n,dtype=np.uint64)
 def B(v):
  t=(Mt@(S*v%p64))%p64
  q=W*t%p64
  return S*((M@q)%p64)%p64
 bp=S*b%p64
 degree_bound=min(n,m+1) # rank(B)<=m implies minpoly(B) degree<=rank(B)+1
 steps=2*degree_bound+64;seq=np.zeros(steps,dtype=np.uint64);v=bp.copy()
 for k in range(steps):
  seq[k]=np.dot(u,v)%p64
  if k+1<steps:v=B(v)
  if progress and (k+1)%2000==0:print(f'KRYLOV {k+1}/{steps} seconds={time.time()-t0:.1f}',flush=True)
 if outprefix:
  np.savez_compressed(str(outprefix)+'_krylov.npz',seq=seq,S=S,W=W,u=u,b=b)
 co=bm(seq,p);L=len(co)-1
 if progress:print(f'MINPOLY degree={L} zero_multiplicity={next((i for i,c in enumerate(co)if c),len(co))} seconds={time.time()-t0:.1f}',flush=True)
 # Check all scalar recurrence equations using exact modular polynomial convolution.
 from flint import nmod_poly
 C=nmod_poly(list(map(int,co[::-1])),p)
 conv=(C*nmod_poly(list(map(int,seq)),p)).coeffs()
 assert all(int(conv[k])==0 for k in range(L,steps) if k<len(conv))
 def evaluate(coeffs):
  v=np.zeros(n,dtype=np.uint64)
  for k in range(len(coeffs)-1,-1,-1):
   if k<len(coeffs)-1:v=B(v)
   if coeffs[k]:v=(v+np.uint64(coeffs[k])*bp)%p64
   if progress and k%2000==0:print(f'EVALUATE remaining={k} seconds={time.time()-t0:.1f}',flush=True)
  return v
 if co[0]:
  # m(B)bp=0 implies B^-1 bp=-(co[1]+...+B^(L-1))/co[0].
  h=(-co[1:].astype(object)*pow(int(co[0]),-1,p))%p
  y=evaluate(list(map(int,h)))
  x=W*((Mt@(S*y%p64))%p64)%p64
  residual=(M@x)%p64
  if np.array_equal(residual,b):return {'kind':'solution','x':x,'degree':L,'seconds':time.time()-t0,'seed':seed}
  return {'kind':'retry','reason':'projected minimal polynomial did not reconstruct a solution','degree':L,'seconds':time.time()-t0}
 nu=next(i for i,c in enumerate(co)if c)
 if nu!=1:return {'kind':'retry','reason':f'zero Jordan multiplicity{nu}; change preconditioner','degree':L,'seconds':time.time()-t0}
 z=evaluate(list(map(int,co[1:])))
 w=S*z%p64;left=(Mt@w)%p64;dot=int(np.dot(w,b)%p64)
 if not np.any(left) and dot:return {'kind':'left_witness','w':w,'dot':dot,'degree':L,'seconds':time.time()-t0,'seed':seed}
 return {'kind':'retry','reason':'zero projection not a verified separating left witness','leftResidualNonzero':int(np.count_nonzero(left)),'dot':dot,'degree':L,'seconds':time.time()-t0}

def selftest():
 p=101;rng=np.random.default_rng(44)
 # Full row-rank consistent system and rank-deficient inconsistent system.
 M=csr_matrix(np.array([[1,2,3],[4,1,7]],dtype=np.uint64));b=np.array([9,8],dtype=np.uint64)
 r=solve(M,b,p,11,progress=False);assert r['kind']=='solution',r
 M=csr_matrix(np.array([[1,2,3],[2,4,6],[0,1,3]],dtype=np.uint64));b=np.array([1,3,7],dtype=np.uint64)
 r=solve(M,b,p,13,progress=False);assert r['kind']=='left_witness',r
 # Rank-deficient but consistent case has no zero-eigen component in bp.
 b=(M@np.array([3,4,8],dtype=np.uint64))%p
 r=solve(M,b,p,17,progress=False);assert r['kind']=='solution',r
 # Large-prime entries force reduction between sparse dots and diagonal products.
 M=csr_matrix(rng.integers(0,PDEFAULT,size=(30,35),dtype=np.uint64))
 b=rng.integers(0,PDEFAULT,size=30,dtype=np.uint64)
 r=solve(M,b,PDEFAULT,23,progress=False);assert r['kind']=='solution',r
 # Very tall matrices exercise the rank-based Krylov length, not the row count.
 M=csr_matrix(rng.integers(0,PDEFAULT,size=(200,6),dtype=np.uint64))
 b=(M@rng.integers(0,PDEFAULT,size=6,dtype=np.uint64))%PDEFAULT
 r=solve(M,b,PDEFAULT,31,progress=False);assert r['kind']=='solution'and r['degree']<=7,r
 b=rng.integers(0,PDEFAULT,size=200,dtype=np.uint64)
 r=solve(M,b,PDEFAULT,37,progress=False);assert r['kind']=='left_witness'and r['degree']<=7,r
 print('PASS six verified solver tests, including large-prime overflow and very tall systems',flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('matrix',nargs='?');ap.add_argument('rhs',nargs='?');ap.add_argument('--prefix');ap.add_argument('--seed',type=int,default=2036);ap.add_argument('--prime',type=int,default=PDEFAULT);args=ap.parse_args()
 selftest()
 if args.matrix:
  out=Path(args.prefix) if args.prefix else ROOT/'wiedemann_result'
  M=load_npz(args.matrix);b=np.load(args.rhs);print(f'START shape={M.shape} nnz={M.nnz} prime={args.prime}',flush=True)
  res=solve(M,b,args.prime,args.seed,out)
  if 'x'in res:np.save(str(out)+'_solution.npy',res.pop('x'))
  if 'w'in res:np.save(str(out)+'_left_witness.npy',res.pop('w'))
  out.with_suffix('.json').write_text(json.dumps(res,indent=2)+'\n');print('VERIFIED_RESULT',res,flush=True)
