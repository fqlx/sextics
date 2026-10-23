from pathlib import Path
import sympy as s,pickle,json
root=Path(__file__).parent
P=pickle.load(open(root/'physical_model.pickle','rb'));k,q,h,sl,ti,v=[P['symbols'][n]for n in ['k','q','h','s','t','v']]
ell,Z=s.symbols('ell Z');a1,a0,b2,b1,b0=[P['coefficients'][n]for n in ['a1','a0','b2','b1','b0']]
c2=3*sl**2*ti+a1*sl+b2;c1=3*sl*ti**2+a1*ti+a0*sl+b1;c0=ti**3+a0*ti+b0
r=v+1/v;sigma=4*ell/v;pi=4*ell+4*ell/v**2-4;Q=k*k-sigma*k+pi;C=sl**3*(k-r)*Q
X=v*(k*k-4)/(4*(k-r));Y=Z*(k-2/v)/(k-r)**2
assert s.cancel((Y*Y-64*(sl/v)**3*X*(X-1)*(X-ell)).subs(Z*Z,(k*k-4)*C))==0
assert s.cancel(s.diff(X,k)/(Y/Z)-v*(k-2*v)/4)==0
E=[v*c2+sl**3*(v*v+1+4*ell),v*v*c1-sl**3*((8*ell-4)*v*v+8*ell),v**3*c0+4*sl**3*(v*v+1)*((ell-1)*v*v+ell)]
(root/'legendre_model.pickle').write_bytes(pickle.dumps((P|dict(ell=ell,equations=E,cubic=C,X=X,Y=Y))))
ans=dict(X=str(X),Y=str(Y),equation='Y²=64(s/v)³X(X-1)(X-ell)',differential='dX/Y=(v/4)(k-2v)dk/Z',smooth_if='s*v*(v²-1)*(v²-ell)*ell*(ell-1) != 0',twist='s/v',j1728='ell=1/2',j0='ell²-ell+1=0')
(root/'legendre_checks.json').write_text(json.dumps(ans,indent=2));print(json.dumps(ans,indent=2))
