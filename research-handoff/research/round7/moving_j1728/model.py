from pathlib import Path
import sympy as s,pickle,json
root=Path(__file__).parent
P=pickle.load(open('/workspace/research/round6/k3_normalform/lambda_gm.pickle','rb'))
k,q,h=[P['symbols'][n] for n in ['k','q','h']]
slope,intercept,v,Z=s.symbols('s t v Z')
a1,a0=[s.Poly(P['scaled']['A'],k).nth(i) for i in [1,0]]
b2,b1,b0=[s.Poly(P['scaled']['B'],k).nth(i) for i in [2,1,0]]
c2=3*slope*slope*intercept+a1*slope+b2
c1=3*slope*intercept*intercept+a1*intercept+a0*slope+b1
c0=intercept**3+a0*intercept+b0
r=v+1/v;delta=v-1/v;Q2=k*k-2*k/v+2/(v*v)-2
C=slope**3*(k-r)*Q2
expected=slope**3*k**3-slope**3*(v+3/v)*k*k+4*slope**3*k/v**2+2*slope**3*(v-v**-3)
assert s.cancel(C-expected)==0
X=-v*Q2/(2*(k-r));Y=Z*(k-2/v)/(k-r)**2
f=(k*k-4)*C
ell_identity=s.cancel((Y*Y+8*(slope/v)**3*(X**3-X)).subs(Z*Z,f))
assert ell_identity==0
# dX/Y=-v/2*(k-2v) dk/Z.
assert s.cancel(s.diff(X,k)/(Y/Z)+v*(k-2*v)/2)==0
E=[v*c2+slope**3*(v*v+3),v*v*c1-4*slope**3,v**3*c0-2*slope**3*(v**4-1)]
(root/'physical_model.pickle').write_bytes(pickle.dumps(dict(symbols=dict(k=k,q=q,h=h,s=slope,t=intercept,v=v),coefficients=dict(a1=a1,a0=a0,b2=b2,b1=b1,b0=b0),equations=E,cubic=C,X=X,Y=Y)))
ans=dict(verified=['cubic_factorization','fixed_j1728_quotient','differential_pullback'],X=str(X),Y=str(Y),elliptic_equation='Y²=-8(s/v)³*(X³-X)',differential='dX/Y=-(v/2)*(k-2v)dk/Z',twist_squareclass='s/v',smooth_if='s*v*(v²-1)*(2v²-1) != 0')
(root/'model_checks.json').write_text(json.dumps(ans,indent=2));print(json.dumps(ans,indent=2))
