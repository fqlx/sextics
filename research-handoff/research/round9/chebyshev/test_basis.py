import pickle,sympy as S,json
from pathlib import Path
P=Path(__file__).parent;d=pickle.loads((P/'physical_model.pickle').read_bytes());q,h,s=[d['symbols'][x]for x in('q','h','s')];r=h*h-4;a1,a0,b2,b1,b0=[d['coefficients'][x]for x in('a1','a0','b2','b1','b0')]
B=S.zeros(6);C=S.zeros(6)
B[:,0]=S.Matrix([0,1,0,0,0,0]);B[:,1]=S.Matrix([0,0,1,0,0,0]);B[:,2]=S.Matrix([0,0,0,1,0,0]);B[:,3]=S.Matrix([0,-b1/3,-a0/3,0,-a1/9,-S.Rational(1,9)]);B[:,4]=S.Matrix([b2,0,0,0,0,0]);B[:,5]=S.Matrix([0,0,0,0,b2,0])
C[:,0]=S.Matrix([0,0,0,0,1,0]);C[:,1]=S.Matrix([b2,0,0,0,0,0]);C[:,2]=S.Matrix([0,b2,0,0,0,0]);C[:,3]=S.Matrix([0,0,b2,0,0,0]);C[:,4]=S.Matrix([0,0,0,0,0,1]);C[:,5]=S.Matrix([-3*b1*b2,-3*a0*b2,0,-9*b2,0,-a1])
I=S.eye(6);e=I[:,0];ops=[I,B,B*B,(B**3+a0*B/3)/r,C/r,C*C/(h*r**3)];T=S.Matrix.hstack(*[x*e for x in ops]);Ti=T.inv();res=[]
for i,op in enumerate(ops):
 M=(Ti*op*T).applyfunc(S.cancel);bad=[]
 for j,v in enumerate(M):
  den=S.denom(v)
  if S.Poly(den,q,h).total_degree()>0:bad.append((j,str(S.factor(den))))
 res.append({'i':i,'nonpolynomial':bad});print(res[-1],flush=True)
(P/'candidate_basis_test.json').write_text(json.dumps(res,indent=2))
