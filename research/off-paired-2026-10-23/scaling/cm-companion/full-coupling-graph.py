#!/usr/bin/env python3
"""Exact full-B CM graph and its physical divisor; not a certificate."""
import json
from pathlib import Path
import sympy as s

q,d,gamma=s.symbols('q d gamma')
X=gamma/q**2
Y=2*d/q**3
j=(1-16*q**6)/(gamma**2*q**2)
roots=[-4*q**2/gamma,
       2*q**2/gamma+s.I*d/(gamma*q),
       2*q**2/gamma-s.I*d/(gamma*q)]

def reduce_numerator(expr):
    num=s.together(expr).as_numer_denom()[0]
    num=s.rem(s.expand(num),gamma**3-4,gamma)
    return s.rem(num,d**2-(1-4*q**6),d)

checks={
    'density_map_to_E_minus16':reduce_numerator(Y**2-X**3+16)==0,
    'isogeny_j_coordinate':reduce_numerator(j-(X**3-64)/(4*X**2))==0,
}
for i,r in enumerate(roots):
    checks[f'normalized_cubic_root_{i+1}']=reduce_numerator(r**3+j*r+1)==0
checks['root_sum']=s.factor(sum(roots))==0
checks['root_product']=reduce_numerator(s.prod(roots)+1)==0

H,Yblock,M,T,K=s.symbols('H Yblock M T K')
F=H+Yblock+M
D54=16*K*M**3*T**4-H**2*Yblock*(T**2-16*K)**3
D18=Yblock*T**2+16*H*K
Q36=(16*K*Yblock**2*T**2+48*K*H*Yblock*T**2
     -256*K**2*H*Yblock+H**2*T**4)
lift=16*K*T**4*F*(M**2-M*(H+Yblock)+(H+Yblock)**2)
checks['physical_factorization_mod_F']=s.expand(D54+D18*Q36-lift)==0

# The cubic of the finite-cover graph equation clears its roots exactly.
a,b,h,c,B=s.symbols('alpha beta h c B')
S,P=s.symbols('S P') # S=H-1=alpha^6, P=x^6*a^6=q^6*S^2
graph_cube=(16*q**6*B**3-h**6*c**3*(1-16*q**6)**3)
cleared=s.expand(graph_cube.subs(q**6,P/S**2)*S**6)
expected=16*P*B**3*S**4-h**6*c**3*(S**2-16*P)**3
checks['graph_cube_clearing']=s.expand(cleared-expected)==0
assert all(checks.values()), checks

out={
  'status':'Actual cubic splitting on a graph divisor; no source Gysin identity or primitive established.',
  'checks':checks,
  'finite_cover_graph':
    'gamma^2*(xi*eta)^2*B = h^2*c*(1-16*(xi*eta)^6); '
    'gamma^3=4, h^3=H, c^3=C, xi^6+eta^6=1.',
  'normalizer_E':{'X':str(X),'Y':str(Y),'j':str(j)},
  'normalized_roots':[str(r) for r in roots],
  'physical_roots':'p_i=(h/c)*r_i, with d=xi^6-eta^6.',
  'physical_polynomial_conventions':{
    'H':'X0^6+X1^6+X2^6',
    'Yblock':'Y0^6+Y1^6+Y2^6',
    'M':'X0^3*X1*Y0*Y1/2+X1^3*X2*Y1*Y2/2+X0^2*X1*X2*Y0*Y2/3',
    'T':'X1^6+X2^6','K':'X1^6*X2^6'},
  'D54':str(D54),'D18':str(D18),'Q36':str(Q36),
  'scope':
    'This is a cubic-resolvent incidence graph j(E_X)=B/(H^(2/3)*C^(1/3)), '
    'not an isogeny graph between the two Fermat elliptic factors. The three '
    'ambient E graphs are torsion translates. Splitting does not establish '
    'nonzero Picard classes, a source-carrying Gysin class, or certificate exactness.',
}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
