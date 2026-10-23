#!/usr/bin/env python3
"""Exact symbolic identities for whole-cubic Y-angle graph supports."""
import json
from pathlib import Path
import sympy as s

H,C,T,W,M=s.symbols('H C T W M')
D54=16*W*T**4*M**3-H**2*C*(T**2-16*W)**3
D18=C*T**2+16*H*W
Q36=16*C**2*T**2*W+48*C*H*T**2*W-256*C*H*W**2+H**2*T**4
checks={}
checks['full_factor_on_F']=s.expand(D54.subs(M,-H-C)+D18*Q36)==0
checks['ambient_divisibility']=s.rem(s.expand(D54+D18*Q36),s.Poly(H+C+M,M),M)==0
q,g=s.symbols('q gamma',nonzero=True)
j=(1-16*q**6)/(g**2*q**2)
checks['graph_j_cube']=s.cancel((j**3-(1-16*q**6)**3/(16*q**6)).subs(g**6,16))==0
# Work with q and y, y^2=q^-6-4, gamma^3=4.
y=s.symbols('y')
r=[-4*q*q/g,(2*q*q+s.I*y*q*q)/g,(2*q*q-s.I*y*q*q)/g]
def red(z):
    n,d=s.fraction(s.cancel(z))
    n=s.rem(s.Poly(n,y),s.Poly(y*y-q**-6+4,y)).as_expr()
    n=s.rem(s.Poly(s.expand(n),g),s.Poly(g**3-4,g)).as_expr()
    return s.cancel(n/d)==0
for k,rr in enumerate(r):
    checks[f'whole_root_{k+1}']=red(rr**3+j*rr+1)
checks['root_sum']=s.cancel(sum(r))==0
out={'checks':checks,'passed':all(checks.values()),'count':len(checks),
     'scope':'Exact whole-cubic support identities; no source primitive or Gysin image.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
assert out['passed']
