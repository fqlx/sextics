from pathlib import Path
import json,time,sympy as S
from pathlib import Path
from sympy.polys.fields import field
from sympy import QQ
st=time.time();u=S.symbols('u');P=S.Function('P')(u);H=S.Function('H')(u);g=S.Function('g')(u);v=H/g;second_inv=v*S.diff(v,u)+S.diff(g,u)*v*v/(2*g);direct=S.diff(P*second_inv,u)+S.diff(S.diff(P,u)*v*v,u)/2;claimed=S.diff(P*v*v,u,2)/2+S.diff(S.diff(g,u)*P*v*v/g,u)/2;assert S.simplify(direct-claimed)==0
# 2/g * d(P2/g)/du on a term u^n has this exact coefficient.
n,ell0=S.symbols('n ell',nonzero=True);gv=3*ell0*u*u;piece=u**n/gv**2;P2=S.diff(piece,u,2)/2+S.diff(2*piece/u,u)/2;op=2/gv*S.diff(P2/gv,u);target=(n-5)*(n-2)*(n-8)*u**(n-11)/(81*ell0**4);assert S.simplify(S.expand_power_base(op-target,force=True))==0
print('PASS exact second inverse-transport formula and 1/81 normalizing factor',flush=True)
b,d,uu,c,z,ell,K=S.symbols('b d u c z ell K');q=1+2*b-uu;r=c*c+2*c*d-z*uu;HH=6*(1+z*c**4)*uu+6*(1+z*z*c*c)*uu**2+(q*q*r+2*q*r*r)/7;PP=(1-uu)*(c*c-z*uu);poly=S.Poly(S.expand(PP*HH**2),b,d,uu);FF,cc,zz,ee,kk=field('c,z,ell,K',QQ);records={}
for (i,j,n),coef in poly.terms():
 n=int(n);v=FF.from_expr(coef)*(n-5)*(n-2)*(n-8)/(81*ee**4)
 if v:records.setdefault((i,j),{})[n-11]=v
res={};radial_expected={}
for (i,j),a in records.items():
 a=a.copy();m=i+j+4;ca={}
 for k in range(-8,0):
  c0=a.get(k-3,FF.zero);ck=c0*ee/(2*k*kk)
  if ck:
   ca[k]=ck
   a[k-3]=a.get(k-3,FF.zero)-(2*k*kk/ee)*ck;a[k]=a.get(k,FF.zero)-(m+2*k)*ck
 radial_expected[(i+1,j+1)]=ca
 assert all(not a.get(k,FF.zero) for k in range(-11,-3))
 for pole in (1,2,3):
  v=a.get(-pole,FF.zero)
  if v:res[(i+1,j+1,pole)]=v
J=json.load(open(Path(__file__).resolve().parent / 'second_character_classification.json'));loc={'c':c,'z':z,'ell':ell,'K':K};saved={(r['b_power'],r['d_power'],r['u_pole']):FF.from_expr(S.sympify(r['coefficient'],locals=loc)) for r in J['residual']};assert saved==res,(len(saved),len(res),set(saved)^set(res));print('PASS all',len(res),'exact classified second-source residual coefficients',round(time.time()-st,2),'seconds',flush=True)

R=json.load(open(Path(__file__).resolve().parent / 'second_source_complete.json')); assert len(R['radials'])==len(radial_expected)
for row in R['radials']:
 key=(row['b_power'],row['d_power']);expr=S.sympify(row['A'],locals={'u':uu,'c':c,'z':z,'ell':ell,'K':K});poly=S.Poly(S.expand(expr*uu**8),uu);got={int(k)-8:FF.from_expr(co) for (k,),co in poly.terms() if co!=0};assert got==radial_expected[key],('radial mismatch',key)
print('PASS all',len(R['radials']),'stored radial coefficients match exact source recurrence',flush=True)
