"""Exact coefficient jets and universal elliptic Gauss-Manin matrices."""
import sympy as s,pickle,json,time
from pathlib import Path
HERE=Path(__file__).parent;U,V,Z=s.symbols('U V Z');A,h,d,e,f,g,k,q,lam=s.symbols('A h d e f g k q lam');vars=(U,V,Z)
C=A*U**3-h*V**3-k*Z**3+d*U**2*V+e*U**2*Z+g*U*V*Z+f*U*Z**2;H=s.expand(s.det(s.hessian(C,vars)));H0=H.subs(e,0);He=s.diff(H,e).subs(e,0);HC=s.hessian(H0,vars);HD=s.hessian(He,vars)
HHp=0
for j in range(3):
 M=HC.copy();M[:,j]=HD[:,j];HHp+=s.det(M)
HHp=s.expand(HHp)
a=s.Rational(9,2)*A*g*h*k-d*f*f*h-g**4/48
b=-A*f**3*h*h+s.Rational(5,8)*A*g**3*h*k+d*d*f*g*h*k+d*f*f*g*g*h/12+g**6/864+k*k*(-s.Rational(27,4)*A*A*h*h+d**3*h)
F0=C.subs(e,0);P=s.Poly(s.expand(HHp-110592*a*a*U*U*Z+13824*b*He),*vars);PF=s.Poly(F0,*vars);PH=s.Poly(H0,*vars)
m=next(m for m,c in PH.terms()if PF.coeff_monomial(m)==0);be=s.factor(-P.coeff_monomial(m)/(13824*PH.coeff_monomial(m)));m=PF.monoms()[0];ae=s.factor((P.coeff_monomial(m)+13824*be*PH.coeff_monomial(m))/(221184*a*PF.coeff_monomial(m)))
assert s.expand(P.as_expr()-221184*a*ae*F0+13824*be*H0)==0
print('I4_e=',ae,flush=True);print('I6_e=',be,flush=True)
physical={A:1+q**6,d:q/2,g:s.Rational(1,3),f:q*q/(4*(h*h-4))};a0=s.factor(a.subs(physical));b0=s.factor(b.subs(physical));eprime=-q*h/(2*(h*h-4));al=s.factor(eprime*ae.subs(physical));bl=s.factor(eprime*be.subs(physical));Delta=s.factor(4*a0**3+27*b0**2)
def gm(da,db):
 z=3*b0*da-2*a0*db;t=2*a0*a0*da+9*b0*db
 return s.Matrix([[-t,a0*z],[3*z,t]])/(2*Delta)
mats={name:gm(s.diff(a0,var),s.diff(b0,var))for name,var in [('k',k),('q',q),('h',h)]};mats['lambda']=gm(al,bl)
# Keep factored coefficient expressions to avoid unhelpful multi-page expansions.
pack={'symbols':{'k':k,'q':q,'h':h},'I4':a0,'I6':b0,'Delta':Delta,'I4_e':ae,'I6_e':be,'I4_lambda':al,'I6_lambda':bl,'matrices':mats,'source':-mats['lambda']*s.Matrix([1,0]),'twistedMatrices':{**mats,'k':mats['k']-k/(k*k-4)*s.eye(2),'h':mats['h']-h/(h*h-4)*s.eye(2)}}
r=h*h-4
at=s.factor(r*r*a0);bt=s.factor(r*r*r*b0);atl=s.factor(r*r*al);btl=s.factor(r*r*r*bl);Deltat=s.factor(4*at**3+27*bt**2)
def gmt(da,db):
 z=3*bt*da-2*at*db;t=2*at*at*da+9*bt*db
 return s.Matrix([[-t,at*z],[3*z,t]])/(2*Deltat)
newmats={name:gmt(s.diff(at,var),s.diff(bt,var))for name,var in [('k',k),('q',q),('h',h)]};newmats['lambda']=gmt(atl,btl)
assert all(s.denom(s.cancel(t))==1 for t in [at,bt,atl,btl])
pack['scaled']={'A':at,'B':bt,'A_lambda':atl,'B_lambda':btl,'Delta':Deltat,'matrices':newmats,'source':-newmats['lambda']*s.Matrix([1,0]),'twistedMatrices':{**newmats,'k':newmats['k']-k/(k*k-4)*s.eye(2)}}
print('SCALED_POLYNOMIAL_A',at,flush=True);print('SCALED_POLYNOMIAL_B',bt,flush=True);print('SCALED_LAMBDA_A',atl,flush=True);print('SCALED_LAMBDA_B',btl,flush=True)
(HERE/'lambda_gm.pickle').write_bytes(pickle.dumps(pack));out={key:str(pack[key])for key in ['I4','I6','Delta','I4_e','I6_e','I4_lambda','I6_lambda','source']};out['matrices']={n:str(M)for n,M in mats.items()};out['scaled']={key:({nn:str(mm)for nn,mm in value.items()}if isinstance(value,dict)else str(value))for key,value in pack['scaled'].items()};(HERE/'lambda_gm.json').write_text(json.dumps(out,indent=2)+'\n');print('SAVED_EXACT_MATRICES',flush=True)
