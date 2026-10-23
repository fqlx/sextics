import sympy as s,pickle,json
from pathlib import Path
x,a,b,da,db=s.symbols('x a b da db');f=x**3+a*x+b;u,v,r0,r1,r2=s.symbols('u v r0 r1 r2');r=r0+r1*x+r2*x*x
cols=[];rs=[]
for n in [0,1]:
 p=s.Poly(-s.Rational(1,2)*x**n*(da*x+db)-(u+v*x)*f-s.diff(r,x)*f+r*s.diff(f,x)/2,x)
 sol=s.solve(p.all_coeffs(),[u,v,r0,r1,r2],dict=True)[0];cols.append([s.factor(sol[u]),s.factor(sol[v])]);rs.append(s.factor(r.subs(sol)))
M=s.Matrix.hstack(*(s.Matrix(v)for v in cols));print('M',M);print('r',rs);print('trace',s.factor(s.trace(M)));print('PASS')
Ma=M.subs({da:1,db:0});Mb=M.subs({da:0,db:1})
assert all(s.factor(t)==0 for t in s.diff(Mb,a)-s.diff(Ma,b)+Ma*Mb-Mb*Ma)
out={'x':x,'a':a,'b':b,'Da':da,'Db':db,'matrix':M,'exactCorrections':rs,'convention':'D(omega_n)=sum_i G[i,n]*omega_i+d_x(r_n/y)'}
h=Path(__file__).parent;(h/'universal_gm.pickle').write_bytes(pickle.dumps(out));(h/'universal_gm.json').write_text(json.dumps({k:str(v)for k,v in out.items()},indent=2)+'\n')
print('UNIVERSAL_FLATNESS_PASS')
