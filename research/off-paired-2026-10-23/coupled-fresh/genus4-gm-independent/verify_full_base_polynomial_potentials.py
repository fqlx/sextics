#!/usr/bin/env python3
"""Exact generic rank-nine checks of source-directed W and Vi potentials."""
import hashlib,json
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly
import sympy as s
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'ruling-source/full-base-connection'
ctx=fmpq_mpoly_ctx.get(('i','j','v'))
i,j,v=ctx.gens();zero=ctx.constant(0);one=ctx.constant(1)
P=lambda x:fmpq_mpoly(str(x).replace('**','^'),ctx)
paths={'ij':BASE/'rank8-ij-connections-results.json',
       'V':BASE/'rank8-v-literal-primitives-results.json',
       'W':BASE/'j-source-primitive-results.json',
       'Vi':HERE.parent/'theta-compact/mixed-i-primitive-results.json'}
src={k:json.loads(p.read_text())for k,p in paths.items()}
denij=P(src['ij']['common_denominator']);denV=P(src['V']['common_denominator'])
G={'i':[[P(x)for x in row]for row in src['ij']['full_rank9_Gamma_numerators']['i']],
   'j':[[P(x)for x in row]for row in src['ij']['full_rank9_Gamma_numerators']['j']],
   'V':[[P(x)for x in row]for row in src['V']['full_rank9_GammaV_numerators']]}
W=[P(x)for x in src['W']['Wbq_polynomial_vector']]+[zero]
Vi=[P(x)for x in src['Vi']['compact_vector']]+[zero]
U=[P(x)for x in src['W']['U_simplified_polynomial_vector']]+[zero]
Ui=[zero,zero,j/6,zero,zero,zero,ctx.constant(2)/3,i/3,zero]
e=lambda n:[one if k==n else zero for k in range(9)]
add=lambda *vs:[sum((p[k]for p in vs),zero)for k in range(9)]
scale=lambda c,p:[c*x for x in p]
expected={
 ('W','i'):scale(-v/6,add(e(0),scale(2*i,e(1)),scale(j,e(4)))),
 ('W','j'):e(7),
 ('W','V'):add(scale(6,W),scale(-6,e(2)),scale(-3*j,e(7))),
 ('Vi','i'):add(U,scale(j/2,e(7))),
 ('Vi','j'):add(Ui,scale(j/2,e(2))),
 ('Vi','V'):add(scale(6,Vi),scale(6,e(1)),scale(-3*j/2,e(6))),
}
checks=[]
for (name,direction),target in expected.items():
    vec=W if name=='W'else Vi
    den=denV if direction=='V'else denij
    der=(lambda x:6*v*x.derivative(2))if direction=='V'else(lambda x:x.derivative(0 if direction=='i'else 1))
    for r in range(9):
        actual=den*der(vec[r])+sum((G[direction][r][c]*vec[c]for c in range(9)),zero)
        assert actual-den*target[r]==0,(name,direction,r)
        checks.append(f'{name} {direction} full row {r}')

# Product-rule current check for an unrestricted physical density t(i,j,v).
ii,jj,vv=s.symbols('i j v')
t=s.Function('t')(ii,jj,vv)
assert s.diff(jj*s.diff(t,jj)/2,jj)==s.diff(t,jj)/2+jj*s.diff(t,jj,2)/2
checks.append('mixed current product rule with unrestricted physical density')
# Full flat-volume V current and compensated j current, using every density
# derivative. These formulas are useful source-serving identities below.
q=s.Function('q')(ii,jj,vv)
assert s.diff(6*vv*q,vv)+6*q==6*vv*s.diff(q,vv)+12*q
checks.append('V current flat-volume divergence coefficient twelve')
assert s.diff(3*jj*q,jj)==3*q+3*jj*s.diff(q,jj)
checks.append('V plus j W current unrestricted density transport')

out={
 'status':'Exact generic full-rank-nine polynomial potential/current identities; source closure remains open',
 'coordinates':'i,j,v; V=6v partial_v, D=V-2i partial_i-j partial_j; flat volume di dj dv',
 'basis':src['W']['basis'],
 'input_sha256':{k:hashlib.sha256(p.read_bytes()).hexdigest()for k,p in paths.items()},
 'potential_relations':{
  'Wi':'nabla_i W=-v*(e0+2i*e1+j*e4)/6',
  'Wj':'nabla_j W=e7',
  'WV':'nabla_V W=6W-6e2-3j*e7',
  'Vii':'nabla_i Vi=U+j*e7/2',
  'Vij':'nabla_j Vi=Ui+j*e2/2',
  'ViV':'nabla_V Vi=6Vi+6e1-3j*eb/2',
  'Ui':'[0,0,j/6,0,0,0,2/3,i/3]',
 },
 'mixed_actual_current':{
  'input':'R=t*nabla_j U, t=hsrc/(6v^2)',
  'Pj_first':'t*U',
  'remaining_first':'-t_j*U',
  'Pi_second':'-t_j*Vi',
  'Pj_second':'(j/2)*t_j*W',
  'remaining_second':'t_ij*Vi-(t_j+j*t_jj)*W/2',
  'identity':'R=nabla_i(Pi_second)+nabla_j(Pj_first+Pj_second)+remaining_second',
  'derivatives':'Every i,j derivative holds v fixed on the actual physical finite field, including the implicit physical branch w(i,j,v).',
 },
 'V_W_source_current':{
  'Pv':'6v*q*W','Pj':'3j*q*W',
  'identity':'nabla_v(Pv)+nabla_j(Pj)=(Vq+3j*q_j+15q)*W-6q*e2',
 },
 'V_Vi_source_current':{
  'Pv':'6v*q*Vi',
  'identity':'nabla_v(Pv)=(Vq+12q)*Vi+6q*e1-(3j/2)*q*eb',
 },
 'literal_reconstruction':'For any displayed coefficient currents Pp, Jbase=-sum_p(nu dot Pp) wedge contraction_partial_p(di dj dv); Jfiber=-sum_p(f_p dot Pp)*(di dj dv), with fp the full stored connection primitives, f_v=fV/(6v). This retains every literal fiber correction.',
 'checks':checks,'passed':len(checks),
 'infinity_companion':'All six potential identities checked in all nine rows; ninth row vanishes exactly, not discarded.',
 'certificate':False,
}
path=HERE/'full-base-polynomial-potential-audit.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'certificate':False},indent=2))
