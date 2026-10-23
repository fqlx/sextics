"""Exact normalization-generator identities on the blown-up D32 near Gamma."""
from pathlib import Path
import sympy as s,pickle,json
H=Path(__file__).parent;p=pickle.load(open(H/'initial.pickle','rb'));a,b,t,v=p['variables'];e=s.Symbol('e');S=a**6+t**6
parts={}
for d in [13,15]:
 f=p['parts'][d].as_expr();q=s.cancel(f.subs(b,0)/S**2);r=s.cancel(s.diff(f,b).subs(b,0)/S);ss=s.cancel((f-q*S*S-b*r*S)/(b*b))
 parts[d]=tuple(s.Poly(u,a,b,t,v).as_expr() for u in [q,r,ss])
q=parts[13][0]+e*e*parts[15][0];r=parts[13][1]+e*e*parts[15][1];ss=parts[13][2]+e*e*parts[15][2];f=p['parts'][13].as_expr()+e*e*p['parts'][15].as_expr()
assert s.expand(f-q*S*S-b*r*S-b*b*ss)==0
assert s.expand((q*S/b)**2+r*(q*S/b)+q*ss-q*f/b**2)==0
# The two roots of theta over b=S=0 differ by r.  r has a simple exact residue.
rr=s.Poly(r.subs(b,0),a).rem(s.Poly(S,a)).as_expr();rr=s.factor(rr)
result=dict(strictTransform='f13+e^2*f15',q13=str(s.factor(parts[13][0])),q15=str(s.factor(parts[15][0])),r13=str(s.factor(parts[13][1])),r15=str(s.factor(parts[15][1])),rModuloNodeIdeal=str(rr),integralGenerator='theta=q*(a^6+t^6)/b',generatorDegree=6,conductorIdealGeneric='(b,a^6+t^6)',normalizationQuotientGeneric='A/(b,a^6+t^6) shifted by degree6',identitiesCheckedExactly=True,scope='Generic Gamma (v^6+1)*(196v^6+171)!=0, after blowing up its ideal (Y0,Y1,Y2). Does not settle special ramification points, infinity, or global H20/source image.')
(H/'strict_normalization.json').write_text(json.dumps(result,indent=2)+'\n');pickle.dump(dict(variables=(a,b,t,v,e),S=S,f=f,q=q,r=r,s=ss,parts=parts),open(H/'strict_normalization.pickle','wb'))
print(json.dumps(result,indent=2))
