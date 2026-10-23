"""Rigorous structural pole bounds for the physical normal defects."""
from pathlib import Path
import pickle,json
from flint import fmpq_mpoly_ctx,fmpq_mpoly
root=Path(__file__).parent;p=pickle.loads((root/'verified.pickle').read_bytes());ctx=fmpq_mpoly_ctx.get(p['variables']);out=[]
for k,V in enumerate(p['fields']):
    terms=[]
    for j,e in enumerate(V):
        f=fmpq_mpoly(e['numerator'],ctx);assert fmpq_mpoly(e['denominator'],ctx).is_constant()
        es=[tuple(map(int,e))for e in f.to_dict()];ua=max(2*i+a+b+c for i,a,b,c in es);ub=max(0,max(a-3*b-c for i,a,b,c in es));uv=max(c for i,a,b,c in es)
        bound=dict(A=ua,b=ub,E=ub,V310=uv,S=0,Delta47=0)
        if j<3:
            bound['A']+=2;bound['V310']+=2;bound['S']=2;bound['Delta47']=1
            if j==2:bound['b']+=2;bound['E']+=3
        terms.append(bound)
    out.append(dict(pivot=k,denominator_bound={name:max(t[name]for t in terms)for name in terms[0]}))
ans=dict(mark_ratio='Teff=b*(1+a*v)*U625/(A*V310), up to nonzero rational units',psi_bounds=out,
         Delta47='Native physical determinant factor, detJac=(1215/343)b²E S²Delta47/A⁵',
         proof='Weighted substitution L=H/(3A²),r=J/(bEA),x=3(bE)³/A,Teff=bEU/(AV); gradients of Teff have denominator dividing A²V²; canonical inverse fields have poles only S²Delta47 and, for Vx, b²E³.',
         normalizing_zero_divisor='Xi_p=D_p*psi_p, where D_p is the displayed denominator monomial. Xi_p is an exactly specified polynomial arithmetic circuit; its irreducible factorization is not asserted.',
         scope='Rigorous pole-clearing bounds, not claimed reduced exponents or a factorization of the new pivot-zero divisor.')
(root/'psi_pole_bounds.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
