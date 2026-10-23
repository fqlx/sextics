#!/usr/bin/env python3
"""Fixed elliptic Galois closure of the actual normalized cubic."""
import sympy as s
import json
X,Y,r=s.symbols('X Y r',nonzero=True)
E=Y**2-X**3+16
j=(X**3-64)/(4*X**2)
r0=-4/X
U=4*j
V=-Y*(X**3+128)/X**3
red=lambda f:s.rem(s.together(f).as_numer_denom()[0],E,Y)==0
checks={
 'cubic':s.factor(r0**3+j*r0+1)==0,
 'resolvent':red(V**2-U**3-432),
 'discriminant_factor':s.factor(4*(-(r**3+1)/r)**3+27+(2*r**3-1)**2*(r**3+4)/r**3)==0,
}
# Deck translation by P=(0,4*i), interpreted as pullback T* f(Q)=f(Q+P).
I=s.I
XT=-8*(4+I*Y)/X**2
YT=-Y+(Y-4*I)*(X-XT)/X
XTm=-8*(4-I*Y)/X**2
checks['translation_on_curve']=red(YT**2-XT**3+16)
checks['translation_fixes_j']=red((XT**3-64)/(4*XT**2)-j)
checks['three_roots_trace_zero']=red(-4/X-4/XT-4/XTm)
checks['three_roots_pairwise']=red(16/(X*XT)+16/(X*XTm)+16/(XT*XTm)-j)
checks['three_roots_product']=red((-4/X)*(-4/XT)*(-4/XTm)+1)
R0=lambda rr: j*rr/(j+3*rr**2)**3
checks['actual_source_trace_zero']=red(R0(-4/X)+R0(-4/XT)+R0(-4/XTm))
# Actual normalization: p=rho*r, H=C*rho^3, B=C*rho^2*j gives R=R0/(HC).
rho,C=s.symbols('rho C',nonzero=True)
p=rho*r0
H=C*rho**3
B=C*rho**2*j
g=3*C*p**2+B
checks['physical_source_normalization']=s.factor(H*C*B*p/g**3-R0(r0))==0
assert all(checks.values()),checks
print(json.dumps({'all_passed':True,'checks':checks,
 'normalization':'rho^3=H/C; p=-4rho/X; j=B/(C rho^2)',
 'T':'pullback by Q -> Q+(0,4i)'},indent=2))
