#!/usr/bin/env python3
import json
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly
p=Path(__file__).with_name('rank8-descended-connection-results.json');data=json.loads(p.read_text());i,j,v,z=s.symbols('i j v z');C=fmpq_mpoly_ctx.get(('i','j','v'))
D=fmpq_mpoly(data['GammaV_denominator'],C)
def vcoef(f,k):return s.Poly.from_dict({(ii,jj):s.Rational(str(a)) for (ii,jj,vv),a in f.to_dict().items() if vv==k},(i,j)).as_expr()
G=[[fmpq_mpoly(t,C) for t in ar] for ar in data['GammaV_numerator']]
D0=vcoef(D,0);R0=s.Matrix(8,8,lambda a,b:s.cancel(vcoef(G[a][b],0)/(6*D0)))
print('D0',s.factor(D0),flush=True);print('residue0',R0,flush=True)
print('charpoly0 start',flush=True);char0=s.factor(R0.charpoly(z).as_expr());print('charpoly0',char0,flush=True)
deg=D.degrees()[2]
maxdeg=max(f.degrees()[2] for ar in G for f in ar if f)
print('D degree',deg,'Gmaxdegree',maxdeg,flush=True)
assert maxdeg<=deg
Rinf=s.Matrix(8,8,lambda a,b:-s.cancel(vcoef(G[a][b],deg)/(6*vcoef(D,deg))))
print('charpoly infinity start',flush=True);charinf=s.factor(Rinf.charpoly(z).as_expr());print('charpolyinf',charinf,flush=True)
# All finite discriminant points are simple nodal degenerations; verify nilpotence
# uniformly without adjoining a discriminant root: numerator residue squared mod D.
# R_alpha=G(alpha)/(6alpha D'(alpha)). Nilpotence follows if G² vanishes modulo D.
# Perform exact polynomial remainder using coefficient field Q(i,j).
DD=s.Poly(str(D).replace('^','**'),v,domain=s.QQ.frac_field(i,j))
GG=[[s.Poly(str(f).replace('^','**'),v,domain=DD.domain) for f in ar] for ar in G]
N2=[[sum((GG[a][k]*GG[k][b] for k in range(8)),s.Poly(0,v,domain=DD.domain)).rem(DD) for b in range(8)] for a in range(8)]
nilpotent=all(f.is_zero for ar in N2 for f in ar)
print('finite residues square zero',nilpotent,flush=True)
out=p.with_name('connection-local-exponents-results.json');out.write_text(json.dumps({'v0_residue':[[str(x) for x in R0.row(k)] for k in range(8)],'v0_charpoly':str(char0),'vinfinity_residue':[[str(x) for x in Rinf.row(k)] for k in range(8)],'vinfinity_charpoly':str(charinf),'D_degree':deg,'G_degree':maxdeg,'finite_discriminant_residues_square_zero':nilpotent},indent=2)+'\n');print('saved',out,flush=True)
