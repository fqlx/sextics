#!/usr/bin/env python3
"""Uniform normal residue interface for actual remaining discriminant poles."""
import json
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly
p=Path(__file__).parent;g=json.loads((p/'rank8-descended-connection-results.json').read_text());ij=json.loads((p.parent/'ruling-source/full-base-connection/rank8-ij-connections-results.json').read_text())
C=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=C.gens();D=fmpq_mpoly(g['GammaV_denominator'],C);JD=fmpq_mpoly(ij['common_denominator'],C);rat,rem=divmod(JD,D);assert not rem;rat=rat.to_dict()[(0,0,0)]
G=[[fmpq_mpoly(z,C) for z in ar] for ar in g['GammaV_numerator']];Gi=[[fmpq_mpoly(z,C)/rat for z in ar] for ar in ij['Gamma_numerators']['i']];Gj=[[fmpq_mpoly(z,C)/rat for z in ar] for ar in ij['Gamma_numerators']['j']]
checks={}
for name,H,der in [('i',Gi,D.derivative(0)),('j',Gj,D.derivative(1))]:
 for a in range(8):
  for b in range(8):
   q,r=divmod(6*v*D.derivative(2)*H[a][b]-der*G[a][b],D)
   assert not r,(name,a,b)
 checks['all_64_normal_residue_identities_'+name]=True
# v inverse modulo D is explicit cubic, because D(v0) is a nonzero constant.
D0=C.from_dict({(a,b,0):z for (a,b,k),z in D.to_dict().items() if not k});assert D0.degrees()==(0,0,0)
q,rem=divmod(D-D0,v);assert not rem
vinv=-q/D0.to_dict()[(0,0,0)]
checks['explicit_v_inverse_mod_D']=v*vinv+C.constant(1)*0+(D-D0)/D0.to_dict()[(0,0,0)]==0
# Correct polynomial identity v*vinv=1-D/D0.
assert v*vinv==1-D/D0.to_dict()[(0,0,0)]
checks['explicit_v_inverse_mod_D']=True
out=p/'discriminant-normal-residue-results.json';out.write_text(json.dumps({'status':'Exact normal residue interface; no actual discriminant current yet claimed','curve_denominator':str(D),'normal_residue_identity':'6v D_v Gamma_p_num-D_p GammaV_num is divisible byD, p=i,j','v_inverse_mod_D':str(vinv),'interpretation':'Every simple discriminant pole of the actual remaining source lies in the common nilpotent residue image. A source-carrying normal current still must retain physical transport and all poles it introduces.','checks':checks,'certificate':False},indent=2)+'\n');print('passed128matrixentries+v-inverse; saved',out)
