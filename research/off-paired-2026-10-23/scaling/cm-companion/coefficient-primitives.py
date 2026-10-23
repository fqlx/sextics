#!/usr/bin/env python3
"""Exact cubic coefficient primitives; these are not physical currents."""
import json
from pathlib import Path
import sympy as s

p,H,B,C=s.symbols('p H B C')
f=C*p**3+B*p+H
g=s.diff(f,p)
R=B*p/g**3
qh=B/(6*C*g)
qb=-p/(2*g)
qc=-1/(2*p*g)

def deriv(q, v):
    return s.diff(q,v)-s.diff(f,v)*s.diff(q,p)/g

def eqmod(expr):
    num=s.fraction(s.factor(expr))[0]
    return s.rem(num,f,p)==0

checks={
    'H_primitive':s.factor(deriv(qh,H)-R)==0,
    'B_primitive':s.factor(deriv(qb,B)-R)==0,
    'C_primitive':s.factor(deriv(qc,C)-R)==0,
    'C_tracefree_proportionality':eqmod(qc-1/(6*H)-2*C*qh/H),
    'H_potential_B_derivative':eqmod(deriv(qh,B)+3*H*R/(2*B)),
    'H_potential_C_derivative':eqmod(deriv(qh,C)-H*R/(2*C)+qh/C),
    'B_potential_H_derivative':eqmod(deriv(qb,H)+(2*B*R+qb)/(3*H)),
    'B_potential_C_derivative':eqmod(deriv(qb,C)+B*R/(3*C)+2*qb/(3*C)),
}
assert all(checks.values()), checks
out={
  'status':'No source-carrying physical current or certificate established.',
  'checks':checks,
  'universal_primitives':{'Q_H':str(qh),'Q_B':str(qb),'Q_C':str(qc)},
  'physical_current_obligation':
    'For Q_H V+Q_B W, the divergence equals '
    'R*(L(V)-2*B*L(W)/(3*H))+'
    'Q_H*(div V-V(C)/C)+'
    'Q_B*(div W-W(H)/(3*H)-2*W(C)/(3*C)), '
    'where L(V)=V(H)-3*H*V(B)/(2*B)+H*V(C)/(2*C).',
}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
