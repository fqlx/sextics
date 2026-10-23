import json
from pathlib import Path
import sympy as s
rho,h,e,V=s.symbols('rho h e V')
q=e/4;r=(rho-2)*h;t=(rho+2)*h
A=V**2+q*V+r; B=V**2-q*V+t; G=A*B
rv=s.cancel((4*V**3*s.diff(G,V)-V**4*s.diff(G,V,2))/(3*s.diff(G,V)**3))
num,den=s.fraction(rv)
num=s.rem(num,A,V);den=s.rem(den,A,V)
red=s.Poly(s.rem(s.expand(num*s.invert(den,A,V)),A,V),V)
f0=s.factor(red.nth(0));f1=s.factor(red.nth(1))
tr=s.factor(2*f0-q*f1);anti=s.factor(f1/2)
expected=16*e*(e**2*rho**3+64*(4-3*rho**2)*h)/(3*(64*h+rho*e**2)**3)
assert s.cancel(tr-expected)==0
out={'rho':'tau+1/tau','d':'tau-1/tau','U':'u/d','V':'v/d','e':'zab/2, invariant','quadratic':'V2+e*V/4+(rho-2)*U3','delta':'2V+e/4','trace':str(tr),'anti_delta_coefficient':str(anti),'reconstruction':'residue = trace/2 + anti_delta_coefficient*(2V+e/4)','source_form':'residue*(dU+rho*U/(rho2-4)drho) wedge (dZ+rho*Z/(rho2-4)drho) wedge da wedge (dB+rho*B/(rho2-4)drho), Z=z/d,B=b/d','status':'Exact source-carrying Ferrari/involution quotient, no primitive.'}
Path(__file__).with_name('ferrari-invariant-source.json').write_text(json.dumps(out,indent=2))
print('trace =',tr)
print('anti =',anti)
