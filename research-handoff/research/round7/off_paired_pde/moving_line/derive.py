from pathlib import Path
import sympy as s,json,pickle
u,v,w,z,j,ell,F=s.symbols('a1 b2 a0 b1 b0 slope f')
k=s.symbols('k')
t=s.cancel((3*w*ell**4+3*z*ell**3-(u*ell+v)**2)/(3*ell**2*(u*ell+2*v)))
c3=ell**3;c2=3*ell**2*t+u*ell+v;c1=3*ell*t**2+u*t+w*ell+z;c0=t**3+w*t+j
assert s.cancel(c2**2-3*c3*c1)==0
X=s.symbols('X')
# Replace k=(X-c2/3)/slope^3 and multiply original y^2 by slope^6.
F6=s.factor(s.cancel(ell**6*c0-c2**3/27))
identity=s.cancel(ell**6*(c3*k**3+c2*k**2+c1*k+c0)-(ell**3*k+c2/3)**3-F6)
assert identity==0
P=s.Poly(s.together(F6-F).as_numer_denom()[0],ell)
root=Path(__file__).parent
(root/'universal_formulas.json').write_text(json.dumps({'t':str(t),'F6':str(F6),'slope_degree':P.degree(),'slope_polynomial':str(s.factor(P.as_expr())),'status':'Universal exact geometric incidence only; no nonzero Gysin/source assertion'},indent=2)+'\n')
(root/'universal_formulas.pickle').write_bytes(pickle.dumps({'t':t,'F6':F6,'slope_polynomial':P.as_expr(),'symbols':(u,v,w,z,j,ell,F)}))
print('t=',t);print('F6=',F6);print('slope degree',P.degree())
