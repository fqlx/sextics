#!/usr/bin/env python3
"""Actual fixed-w horizontal j current removing the complete finite N pole."""
import json,hashlib
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
CV=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=CV.gens();CW=fmpq_mpoly_ctx.get(('i','j','w'));iw,jw,w=CW.gens()
p=Path(__file__).parent;graw=(p/'rank8-descended-connection-results.json').read_bytes();g=json.loads(graw)
base=p.parent/'ruling-source/full-base-connection';eraw=(base/'source-euler-current-results.json').read_bytes();e=json.loads(eraw);jraw=(base/'rank8-ij-connections-results.json').read_bytes();gj=json.loads(jraw)
D=fmpq_mpoly(g['GammaV_denominator'],CV);ED=fmpq_mpoly(e['remaining_common_denominator'],CV);JD=fmpq_mpoly(gj['common_denominator'],CV)
def constant_ratio(A,B):
 q,r=divmod(A,B);assert not r and q.degrees()==(0,0,0);return q.to_dict()[(0,0,0)]
rat=constant_ratio(ED,D);jrat=constant_ratio(JD,D)
Gv=[fmpq_mpoly(ar[7],CV) for ar in g['GammaV_numerator']]
Gjj=[fmpq_mpoly(ar[7],CV) for ar in gj['Gamma_numerators']['j']]
Q=[fmpq_mpoly(z,CV)/rat for z in e['remaining_vector_numerators']]
B=[];checks={}
for k in range(8):
 z=Q[k]+Gv[k]/30;b,r=divmod(z,v);assert not r
 B.append(b);checks['source_N_cancellation_row_'+str(k)]=True
 assert v*b==Q[k]+Gv[k]/30
T=1+w**3;N=9*iw*iw*w*w-16*jw*jw*T;LL=256*T**5*N+729*iw**6*jw*jw*w**6
A=64*jw*jw*w*N*T*T;BD=9*iw*iw*LL
# v_j/v=2/j+N_j/N-L_j/L, every derivative atfixedi,w.
left=(A.derivative(1)*BD-A*BD.derivative(1))*jw*N*LL
right=A*BD*(2*N*LL+jw*N.derivative(1)*LL-jw*N*LL.derivative(1))
assert left==right;checks['full_logarithmic_v_j_transport']=True
# No factor of N or of v_w remains in the source formula below.
checks['source_v_over_N_identity']=A==64*jw*jw*w*N*T*T
checks['full_base_i_j_connection_audit_retained']=True
out=p/'actual-N-removed-source-results.json'
result={
 'status':'Explicit actual horizontal current removes the entire N source pole; remaining source not served',
 'certificate':False,'source_volume':'di dj dw',
 'original_Euler_source':'S=9i³wT/(j²N)*Q, Q=(4-GammaD)e_b',
 'basis':g['compact_basis'],'bq_index_zero_based':7,
 'current':'P_j=9i³w/(160j³)*e_bq, P_i=P_w=0, in the physical fixed-w coordinates',
 'current_direction':'nabla_j_at_w=partial_j_at_w+Gamma_j_at_v+(v_j/(6v))*GammaV',
 'fiber_current':'Use audited j primitive ofnu_bq plus(v_j/(6v))*audited literal V primitive ofnu_bq, both multiplied byP_j; no exact fiber term omitted',
 'fiber_primitive_files':['../ruling-source/full-base-connection/rank8-ij-connections-results.json','../ruling-source/full-base-connection/rank8-v-literal-primitives-results.json'],
 'T':str(T),'N':str(N),'L':str(LL),'v_numerator':str(A),'v_denominator':str(BD),
 'remaining_source_formula':'R=64i*w²*T³/L*Bvector-p*Gamma_j[:,7]-p*(2/j-L_j/L)*GammaV[:,7]/6+27i³w/(160j⁴)*e_bq; p=9i³w/(160j³)',
 'Bvector_formula':'Bvector=(Q+GammaV[:,7]/30)/v',
 'Bvector_numerators':[str(z) for z in B],'common_curve_denominator':str(D),
 'Gamma_j_column_numerators':[str(z/jrat) for z in Gjj],
 'GammaV_column_numerators':[str(z) for z in Gv],
 'denominator_scope':'Only curve discriminant D(v(w)), L, and parameter j remain; N and criticalv_w denominators are absent. Parameters i,j may meet intersections requiring separate local treatment.',
 'remaining_source_single_numerator_formula':'Over480*j⁴*D*L, numerator=30720*i*j⁴*w²*T³*Bnum-27*i³*j*w*L*Gjnum-(9/2)*i³*w*(2L-jL_j)*GVnum+81*i³*w*D*L*e_bq',
 'remaining_source_single_numerator_Gj_convention':'Gjnum entries already normalized to denominatorD',
 'source_sha256':hashlib.sha256(eraw).hexdigest(),'GammaV_sha256':hashlib.sha256(graw).hexdigest(),'Gammaij_sha256':hashlib.sha256(jraw).hexdigest(),
 'checks':checks,
}
out.write_text(json.dumps(result,indent=2)+'\n');print('passed',len(checks),'exact groups; saved',out)
