from pathlib import Path
import json
import sympy as s
v,q,r,t=s.symbols('v q r s')
A=v**2+q*v+r
B=v**2-q*v+t
G=A*B
rv=s.cancel((4*v**3*s.diff(G,v)-v**4*s.diff(G,v,2))/(3*s.diff(G,v)**3))
num,den=s.fraction(rv)
num=s.rem(num,A,v);den=s.rem(den,A,v)
coeff=s.invert(den,A,v)
red=s.Poly(s.rem(s.expand(num*coeff),A,v),v)
f0=s.factor(red.nth(0));f1=s.factor(red.nth(1))
tr=s.factor(2*f0-q*f1)
odd=s.factor(f1/2)
print('trace =',tr)
print('delta coefficient =',odd)
out={'quadratic':'v2+qv+r','other_quadratic':'v2-qv+s','residue':'Res v4 dv/(3G2)','trace':str(tr),'delta_coefficient':str(odd),'reconstruction':'residue(v)=trace/2+delta_coefficient*(2v+q)','status':'Finite-source trace and reconstruction; no primitive; trace alone loses the delta component.'}
Path(__file__).with_name('ferrari-trace.json').write_text(json.dumps(out,indent=2))
