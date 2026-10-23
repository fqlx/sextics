"""Explicit normalization of the generic degree13 transverse cone.
The full D32 deformation and finite special-v collisions require extra work.
"""
from pathlib import Path
import pickle,json,sympy as s
H=Path(__file__).parent
p=pickle.load(open(H/'initial.pickle','rb'));a,b,t,v=p['variables'];f=p['parts'][13].as_expr()
S=a**6+t**6
q=s.cancel(f.subs(b,0)/S**2)
r=s.cancel(s.diff(f,b).subs(b,0)/S)
ss=s.cancel((f-q*S**2-b*r*S)/b**2)
q=s.Poly(q,a,b,t,v).as_expr();r=s.Poly(r,a,b,t,v).as_expr();ss=s.Poly(ss,a,b,t,v).as_expr()
assert s.expand(f-q*S**2-b*r*S-b*b*ss)==0
assert s.Poly(q,a,b,t).total_degree()==1
assert s.Poly(r,a,b,t).total_degree()==6
assert s.Poly(ss,a,b,t).total_degree()==11
assert s.expand((q*S/b)**2+r*q*S/b+q*ss-q*f/b**2)==0
# At each of the six collinear nodes, ordinary-node determinant.
Hess=s.expand((r*r-4*q*ss).subs(b,0))
HH=s.Poly(Hess,a).rem(s.Poly(a**6+t**6,a)).as_expr()
# Return to projective chart t1 and use aa^6=-1.
node_discriminant=s.factor(s.resultant(HH.subs(t,1),a**6+1,a))
result=dict(multiplicity=13,nextNormalDegree=15,initialTerms=len(p['parts'][13].terms()),nextTerms=len(p['parts'][15].terms()),nodeEquation=str(S),q=str(s.factor(q)),rTerms=len(s.Poly(r,a,b,t,v).terms()),sTerms=len(s.Poly(ss,a,b,t,v).terms()),normalizationGenerator='theta=q*S/b; degree6',identities=['b*theta=q*S','S*theta=-r*S-b*s','theta^2+r*theta+q*s=0'],nodeDiscriminantNorm=str(node_discriminant),normalizationSectionQuotientHilbert='t^6*(1-t^6)/(1-t)^2',scope='Generic function field of Gamma and the initial normal cone; full epsilon^2 deformation and special v loci not concluded.')
(H/'normalization.json').write_text(json.dumps(result,indent=2)+'\n')
with open(H/'normalization.pickle','wb')as h:pickle.dump(dict(variables=(a,b,t,v),f=f,S=S,q=q,r=r,s=ss,nodeDiscriminant=HH),h)
ff=s.Poly(f.subs(v,1),a,b,t).primitive()[1].as_expr(); fs=str(ff).replace('**','^')
script='ring R=1000003,(a,b,t),dp;\npoly f='+fs+';\nprint("FACTORS");\nprint(factorize(f));\nring A=1000003,(a,b),dp;\npoly f='+str(ff.subs(t,1)).replace('**','^')+';\nideal J=f,diff(f,a),diff(f,b);\nJ=std(J);\nprint("AFFINE_JACOBIAN");print(J);print(vdim(J));\nring I=1000003,(b),dp;\nideal Inf='+','.join(str(s.diff(ff,u).subs({a:1,t:0})).replace('**','^') for u in [a,b,t])+';\nprint("INFINITY_CHART_A");print(std(Inf));\nquit;\n'
(H/'node_check_mod.sing').write_text(script)
print(json.dumps(result,indent=2))
