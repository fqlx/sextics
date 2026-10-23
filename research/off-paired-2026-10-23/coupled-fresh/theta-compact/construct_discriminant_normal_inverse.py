#!/usr/bin/env python3
"""Exact small Sylvester inverse of D_i modulo the physical curve discriminant."""
import json,time
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly
C=fmpq_mpoly_ctx.get(('i','j'));i,j=C.gens();V=fmpq_mpoly_ctx.get(('i','j','v'));vi,vj,v=V.gens();zero=C.constant(0);one=C.constant(1)
p=Path(__file__).with_name('rank8-descended-connection-results.json');data=json.loads(p.read_text());D=fmpq_mpoly(data['GammaV_denominator'],V)
def coef(f,k):return C.from_dict({(a,b):z for (a,b,c),z in f.to_dict().items() if c==k})
def inject(f,k=0):return V.from_dict({(a,b,k):z for (a,b),z in f.to_dict().items()})
def main():
 t=time.monotonic();dc=[coef(D,k) for k in range(5)];di=[z.derivative(0) for z in dc]
 hc=[dc[4]*di[k]-di[4]*dc[k] for k in range(4)]
 # Seven unknowns u0..u2,z0..z3, seven coefficients of uD+z h.
 A=[[zero for _ in range(8)] for _ in range(7)]
 for n in range(7):
  for k in range(3):
   if 0<=n-k<=4:A[n][k]=dc[n-k]
  for k in range(4):
   if 0<=n-k<=3:A[n][3+k]=hc[n-k]
  A[n][7]=one if not n else zero
 prev=one
 for k in range(7):
  if not A[k][k]:
   r=next(r for r in range(k+1,7) if A[r][k]);A[k],A[r]=A[r],A[k]
  pivot=A[k][k]
  for rr in range(7):
   if rr==k:continue
   z=A[rr][k]
   for cc in range(8):
    if cc==k:continue
    q,r=divmod(pivot*A[rr][cc]-z*A[k][cc],prev);assert not r
    A[rr][cc]=q
   A[rr][k]=zero
  prev=pivot
 den=A[0][0];nums=[A[k][7] for k in range(7)];common=den
 for z in nums:common=common.gcd(z)
 den=den//common;nums=[z//common for z in nums]
 u=sum((inject(nums[k],k) for k in range(3)),V.constant(0));zz=sum((inject(nums[3+k],k) for k in range(4)),V.constant(0))
 h=inject(dc[4])*D.derivative(0)-inject(di[4])*D
 assert u*D+zz*h==inject(den)
 invnum=inject(dc[4])*zz;quot=u-inject(di[4])*zz
 assert invnum*D.derivative(0)+quot*D==inject(den)
 out=p.with_name('discriminant-normal-inverse-results.json');out.write_text(json.dumps({'status':'Exact generic polynomial normal inverse for actual discriminant source serving; physical current not yet constructed','inverse_D_i_numerator':str(invnum),'inverse_D_i_denominator':str(den),'Bezout_D_coefficient':str(quot),'identity':'inverse_D_i_numerator*D_i+Bezout_D_coefficient*D=inverse_D_i_denominator','normal_ratios':'GammaV ≡ [6v D_v * inverse_D_i] Gamma_i modD; Gamma_j ≡ [D_j*inverse_D_i]Gamma_i modD','checks':{'exact_full_Bezout_identity':True,'denominator_nonzero':bool(den)},'seconds':round(time.monotonic()-t,3),'certificate':False},indent=2)+'\n');print('saved',out,'seconds',round(time.monotonic()-t,2),'den terms',len(den.to_dict()))
if __name__=='__main__':main()
