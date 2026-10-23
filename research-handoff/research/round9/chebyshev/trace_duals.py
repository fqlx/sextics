import sympy as S,pickle,json
from pathlib import Path
P=Path(__file__).parent;s,a0,a1,b1,b2,r,h=S.symbols('s a0 a1 b1 b2 r h');f=s**6+a0*s**4/3+b1*s**3/3+a1*b2*s/9+b2*b2/9
u=-9/b2*(s**5+a0*s**3/3+b1*s*s/3+a1*b2/9);u2=S.rem(u*u,f,s);E=[1,s,s*s,(s**3+a0*s/3)/r,u/r,u2/(h*r**3)];T=S.Matrix(6,6,lambda i,j:S.expand(E[j]).coeff(s,i));Ti=T.inv();raw=S.Matrix([s**5+a0*s**3/3+b1*s*s/3+a1*b2/9,s**4+a0*s*s/3+b1*s/3,s**3+a0*s/3+b1/3,s*s+a0/3,s,1]);g=(Ti*raw).applyfunc(S.factor)
print('trace dual numerators / fprime:');print(g)
(P/'trace_duals.pickle').write_bytes(pickle.dumps({'s':s,'symbols':dict(zip(['a0','a1','b1','b2','r','h'],[a0,a1,b1,b2,r,h])),'g':g,'f':f}));(P/'trace_duals.json').write_text(json.dumps({'denominator':'derivative of monic slope sextic wrt s','numerators':[str(x)for x in g]},indent=2)+'\n')
