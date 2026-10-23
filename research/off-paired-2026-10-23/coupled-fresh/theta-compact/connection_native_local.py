#!/usr/bin/env python3
import json
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly
import sympy as s
p=Path(__file__).with_name('rank8-descended-connection-results.json');data=json.loads(p.read_text());C=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=C.gens();zero=C.constant(0)
D=fmpq_mpoly(data['GammaV_denominator'],C);G=[[fmpq_mpoly(z,C) for z in ar] for ar in data['GammaV_numerator']]
deg=D.degrees()[2];degrees=[[int(f.degrees()[2]-deg) if f else -100 for f in ar] for ar in G]
print('degree excess',degrees,flush=True)
shifts=[0]*8
for turn in range(9):
 changed=False
 for rr in range(8):
  for cc in range(8):
   if G[rr][cc] and shifts[rr]<shifts[cc]+degrees[rr][cc]:shifts[rr]=shifts[cc]+degrees[rr][cc];changed=True
 if not changed:break
else:raise ValueError('positive degree cycle; diagonal shear insufficient')
print('infinity shear exponents',shifts,flush=True)
# For mu_j=v^shifts[j]*nu_j the connection is Fuchsian at infinity.
leadD=C.from_dict({(ii,jj,0):z for (ii,jj,vv),z in D.to_dict().items() if vv==deg})
Rinf=[]
for rr in range(8):
 ar=[]
 for cc in range(8):
  required=deg+shifts[rr]-shifts[cc]
  lead=C.from_dict({(ii,jj,0):z for (ii,jj,vv),z in G[rr][cc].to_dict().items() if vv==required})
  ar.append('-('+str(lead)+')/(6*('+str(leadD)+'))'+('-'+str(shifts[cc]) if rr==cc else ''))
 Rinf.append(ar)
ii,jj,z=s.symbols('i j z');R=s.Matrix([[s.cancel(s.sympify(x,locals={'i':ii,'j':jj})) for x in ar] for ar in Rinf])
print('infinity charpoly start',flush=True);char=s.factor(R.charpoly(z).as_expr());print('infinity charpoly',char,flush=True)
# Uniform exact nodal-residue nilpotence, avoiding an algebraic root of D.
nilpotent=True
for rr in range(8):
 for cc in range(8):
  product=sum((G[rr][k]*G[k][cc] for k in range(8)),zero)
  quo,rem=divmod(product,D)
  if rem:nilpotent=False;print('nonzero residue-square entry',rr,cc,flush=True);break
 if not nilpotent:break
print('all finite discriminant residues square zero',nilpotent,flush=True)
out=p.with_name('connection-native-local-results.json');out.write_text(json.dumps({'v0_charpoly':'(z-1/6)^2*(z-1/3)^2*(z-2/3)^2*(z-5/6)^2','infinity_diagonal_shear':shifts,'infinity_residue':[[str(x) for x in R.row(k)] for k in range(8)],'infinity_charpoly':str(char),'finite_discriminant_residues_square_zero':nilpotent,'degree_excess':degrees},indent=2)+'\n');print('saved',out,flush=True)
