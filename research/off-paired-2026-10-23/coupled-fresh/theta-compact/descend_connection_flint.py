#!/usr/bin/env python3
"""Native exact polynomial descent of generic affine connection to rank eight."""
import json,time
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
C=fmpq_mpoly_ctx.get(('c','d','e'));T=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=T.gens();zero=T.constant(0);one=T.constant(1)
m=[1,2,3,4,5,1,2,4,5]
def descend_dict(poly,shift):
 result={}
 for (cc,dd,ee),coef in poly.to_dict().items():
  n=2*cc+dd+ee+shift;assert n%6==0
  key=(cc,dd,n//6);result[key]=result.get(key,fmpq(0))+coef
 return result

def matmul(A,B):return [[sum((a*b for a,b in zip(ar,bc)),zero) for bc in zip(*B)] for ar in A]
def add(A,B):return [[a+b for a,b in zip(ar,br)] for ar,br in zip(A,B)]
def main():
 t=time.monotonic();path=Path(__file__).with_name('affine-V-generic-results.json');data=json.loads(path.read_text())
 den=fmpq_mpoly(data['common_denominator'],C);k=next(iter(den.to_dict()));r=(2*k[0]+k[1]+k[2])%6
 dd=descend_dict(den,-r);nd=[[descend_dict(fmpq_mpoly(data['gamma_numerators'][rr][cc],C),m[cc]-m[rr]-r) for cc in range(9)] for rr in range(9)]
 minv=min([x[2] for x in dd]+[x[2] for ar in nd for dc in ar for x in dc]);shift=max(0,-minv)
 def mk(dc):return T.from_dict({(cc,jj,vv+shift):coef for (cc,jj,vv),coef in dc.items()})
 D=mk(dd);G=[[mk(dc) for dc in ar] for ar in nd]
 for k in range(9):G[k][k]+=m[k]*D
 cp=i-j*j/4;rr=cp*(cp-j*j)/8
 change=[[zero for _ in range(9)] for _ in range(9)]
 order=[0,1,3,4,5,6,7,8,2]
 for cc,rrr in enumerate(order):change[rrr][cc]=one
 change[2][3]=-v*rr;change[2][5]=j/2
 # Inverse change consists of inverse permutation and the two opposite shears.
 inv=[[zero for _ in range(9)] for _ in range(9)]
 for cc,rrr in enumerate(order):inv[cc][rrr]=one
 inv[8][4]=v*rr;inv[8][6]=-j/2
 ident=matmul(inv,change);assert ident==[[one if r==c else zero for c in range(9)] for r in range(9)]
 deriv=[[6*v*D*z.derivative(2) for z in ar] for ar in change]
 GC=matmul(inv,add(matmul(G,change),deriv))
 assert all(not x for x in GC[8][:8]);assert GC[8][8]==3*D
 # Remove common polynomial factors in the full compact matrix and denominator.
 common=D
 for ar in GC:
  for z in ar:
   common=common.gcd(z)
   if common==1:break
  if common==1:break
 D=D//common;GC=[[z//common for z in ar] for ar in GC]
 cp=i-j*j/4;kappa=j*(v*cp**3+8)/16
 B=[-i*j*(12*i-j*j)*v/840,-i*j*(12*i-j*j)*v/840,-2*j/21,-j*(44*i-7*j*j)/280,i*(12*i-j*j)*v/420,(i*(96*i*i-44*i*j*j+3*j**4)*v-2880)/1680,-(456*i-3*j*j-80)/420,-(208*i-9*j*j)/840]
 out=path.with_name('rank8-descended-connection-results.json')
 result={
 'status':'Exact generic compact rank8 connection; actual Green source still to be integrated',
 'coordinates':'i=c/e²,j=d/e,v=e⁶ with actual v=v(w) retained',
 'descended_curve':'a*y=x³; y²+v*(a²+i*x²+j*a*x+x+1)=0',
 'compact_basis':['1','q','q³','q⁴-Cp*(Cp-d²)*q²/8','a','a*q+d*q²/2','b','b*q'],
 'basis_weights':[1,2,4,5,1,2,4,5],
 'basis_convention':'nu=e^m*N*dq/J; Cp=c-d²/4; ninth omega_hat=e³*q²*dq/J retained before compact restriction',
 'connection_convention':'partial_w nu_j=sum_i Gamma_w[i,j]nu_i+d_q(f_j); columns differentiate basis forms',
 'Gamma_w':'v_w/(6v)*GammaV_numerator/GammaV_denominator',
 'GammaV_denominator':str(D),
 'GammaV_numerator':[[str(z) for z in ar[:8]] for ar in GC[:8]],
 'omega_column_numerator':[str(GC[k][8]) for k in range(8)],
 'both_third_kind_diagonals':'3*v_w/(6v)=v_w/(2v)',
 'omega_theta_compact_vector':[str(z) for z in B],
 'actual_compact_source':'-v_w/(12*j*v²)*(Cd*nu_q3+Ce*nu_b+Cc*nu_bq)',
 'source_equation':'P_w+Gamma_w*P=actual_compact_source',
 'source_definitions':'Finite_residue_cm and source_connection_audit exact Green current; no scalar K remains in compact forcing',
 'checks':{'all_333_generic_polynomial_identities':data['all_333_generic_cleared_polynomial_identities'],'deck_weight_invariance':True,'compact_residue_rows_zero':True,'omega_residue_diagonal_3':True},
 'seconds':round(time.monotonic()-t,3),
 }
 out.write_text(json.dumps(result,indent=2)+'\n');print('saved',out,'seconds',round(time.monotonic()-t,2),flush=True)
 print('v degree',D.degrees()[2], 'den terms',len(D.to_dict()),flush=True)
if __name__=='__main__':main()
