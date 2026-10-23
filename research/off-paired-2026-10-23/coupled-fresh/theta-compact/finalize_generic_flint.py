#!/usr/bin/env python3
"""Resume saved core and keep every arithmetic operation native in FLINT."""
import json,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq
from affine_e_connection import matrix,numerator,BASIS,ROWS,F,c,d,e,a,b,q,J,red,vector
ctx=fmpq_mpoly_ctx.get(('c','d','e'))
def conv(x):return ctx.from_dict({k:fmpq(str(v)) for k,v in s.Poly(x,c,d,e).terms()})
def parse(x):return conv(s.sympify(x))
def main():
 t=time.monotonic();p=Path(__file__).with_name('core-checkpoint-V.json');ck=json.loads(p.read_text())
 rr=ck['rows'];cc=ck['cols'];n=len(rr);m=len(ck['B'][0]);Z=[[parse(z) for z in ar+br] for ar,br in zip(ck['A'],ck['B'])]
 prev=ctx.constant(1)
 for k in range(n):
  if not Z[k][k]:
   r=next(r for r in range(k+1,n) if Z[r][k]);Z[k],Z[r]=Z[r],Z[k]
  pivot=Z[k][k]
  for ii in range(n):
   if ii==k:continue
   z=Z[ii][k]
   for jj in range(n+m):
    if jj==k:continue
    quo,rem=divmod(pivot*Z[ii][jj]-z*Z[k][jj],prev);assert not rem
    Z[ii][jj]=quo
   Z[ii][k]=ctx.constant(0)
  prev=pivot;print('pivot',k+1,flush=True)
 den=Z[0][0];Xs=[Z[ii][n+jj] for ii in range(n) for jj in range(m)]
 common=den
 for z in Xs:
  common=common.gcd(z)
  if common==1:break
 den=den//common;Xs=[z//common for z in Xs]
 Y=[[ctx.constant(0) for _ in range(m)] for _ in range(25)]
 for ii,k in enumerate(cc):
  for jj in range(m):Y[k][jj]=Xs[ii*m+jj]
 for r,k in ck['pivot_pairs']:
  for jj in range(m):Y[k][jj]=parse(ck['full_B'][r][jj])*den-sum((parse(ck['full_A'][r][v])*Y[v][jj] for v in cc),ctx.constant(0))
 print('native reconstruction complete',round(time.monotonic()-t,2),flush=True)
 # Save exact arrays before validation so environment refresh cannot erase work.
 out=p.with_name('affine-V-generic-results.json')
 data={'mode':'V','basis':[str(x) for x in BASIS],'f_words':[str(x) for x in F],'common_denominator':str(den),'primitive_numerators':[[str(x) for x in ar] for ar in Y[:16]],'gamma_numerators':[[str(x) for x in ar] for ar in Y[16:]],'all_333_generic_cleared_polynomial_identities':False,'arithmetic':'FLINT fmpq_mpoly exact Bareiss; arrays not expanded by SymPy','seconds':round(time.monotonic()-t,3)}
 out.write_text(json.dumps(data,indent=2)+'\n');print('arrays saved before audit',flush=True)
 M,_=matrix();U=s.Matrix.hstack(*(vector(red(2*c*numerator(N,c)+d*numerator(N,d)+e*numerator(N,e)),ROWS) for N in BASIS))
 MM=[[conv(x) for x in M.row(rrr)] for rrr in range(37)];UU=[[conv(x) for x in U.row(rrr)] for rrr in range(37)]
 for rrri in range(37):
  for jj in range(9):assert sum((MM[rrri][k]*Y[k][jj] for k in range(25)),ctx.constant(0))==UU[rrri][jj]*den,(rrri,jj)
 data['all_333_generic_cleared_polynomial_identities']=True;data['seconds']=round(time.monotonic()-t,3)
 out.write_text(json.dumps(data,indent=2)+'\n');print('all333 exact generic polynomial identities pass',round(time.monotonic()-t,2),flush=True)
if __name__=='__main__':main()
