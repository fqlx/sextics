from pathlib import Path
import pickle,sympy as s,json
H=Path(__file__).parent;d=pickle.load(open('/workspace/research/round9/abel_prym/effective_graph.pickle','rb'));z=s.symbols('X0 X1 X2 Y0 Y1 Y2');X0,X1,X2,a,b,t=z
D=s.Poly.from_dict({e:s.Rational(c)for e,c in d['D'].items()},*z).as_expr();S=a**6+t**6
q=s.cancel(D.subs(b,0)/S**2);r=s.cancel(s.diff(D,b).subs(b,0)/S);ss=s.cancel((D-q*S*S-b*r*S)/(b*b))
q,r,ss=[s.Poly(f,*z).as_expr()for f in(q,r,ss)]
assert s.expand(D-q*S*S-b*r*S-b*b*ss)==0
result=dict(degreeD=32,degreeS=6,degreeq=s.Poly(q,*z).total_degree(),degreer=s.Poly(r,*z).total_degree(),degrees=s.Poly(ss,*z).total_degree(),thetaDegree=25,terms=[len(s.Poly(f,*z).terms())for f in(q,r,ss)],q=str(s.factor(q)),r=str(s.factor(r)),identityCheckedExactly=True,scope='Finite integral intermediate algebra; full global normality and resolution R1 not concluded.')
pickle.dump(dict(variables=z,D=D,S=S,q=q,r=r,s=ss),open(H/'global_normalization.pickle','wb'));(H/'global_normalization.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
