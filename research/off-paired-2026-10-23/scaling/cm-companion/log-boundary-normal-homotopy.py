#!/usr/bin/env python3
"""Finite normal/log homotopy for the actual Y-Fano boundary source.

This retains the physical logarithmic coefficient. It supplies no primitive
for that coefficient and no off-paired certificate.
"""
import json
from pathlib import Path
import sympy as s

G,P2,da,ea,t=s.symbols('G P2 daux eaux t')
J=G-da**3-ea**3
ge=s.diff(J,ea)
B=P2/(da*ea)
raw=s.factor(s.diff(B/ge,ea)/ge)
# Ambient order du,dv,ddaux,deaux: putting dJ first has sign (-1)^3.
ordered=-raw
checks={
    'raw_normal_scalar':s.factor(raw+P2/(3*da*ea**6))==0,
    'ordered_normal_scalar':s.factor(ordered-P2/(3*da*ea**6))==0,
}
alpha=P2/(9*t*(G-t)**2)
F=P2/(9*G*(G-t))
L=P2/(9*G**2)
ell_t=1/t+1/(G-t)
checks['rational_log_decomposition']=s.factor(alpha-s.diff(F,t)-L*ell_t)==0

# Arbitrary external parameter jet: D(t)=0, D(G)=G_D, D(P2)=P2_D.
Gd,Pd=s.symbols('G_D P2_D')
def D(expr):
    return s.diff(expr,G)*Gd+s.diff(expr,P2)*Pd
ell_D=-Gd/(G-t)
Fd=s.factor(D(F)+L*ell_D)
checks['mixed_log_jet']=s.factor(D(ell_t)-s.diff(ell_D,t))==0
checks['primitive_jet_identity']=s.factor(D(alpha)-s.diff(Fd,t)-D(L)*ell_t)==0

# Actual parameter d=P^3 and actual C+B^3/(27d) source.
d,C,Bphys,Z=s.symbols('d C B Y0_cubed')
Ga=C+Bphys**3/(27*d)
P2a=Z*(C-2*Bphys**3/(27*d))
checks['actual_source_as_parameter_operator']=s.factor(P2a/Ga**2-Z*(1/Ga-3*d*s.diff(1/Ga,d)))==0
Fa=s.factor(F.subs({G:Ga,P2:P2a}))
La=s.factor(L.subs({G:Ga,P2:P2a}))
Fda=s.factor(s.diff(Fa,d)-La*s.diff(Ga,d)/(Ga-t))
checks['actual_d_jet']=s.factor(s.diff(alpha.subs({G:Ga,P2:P2a}),d)
    -s.diff(Fda,t)-s.diff(La,d)*ell_t.subs(G,Ga))==0
assert all(checks.values()),checks

out={
  'status':'Exact finite normal/log chain identity; physical logarithmic coefficient remains unresolved.',
  'checks':checks,
  'orientation':'Ambient order (u,v,daux,eaux); put J first for the displayed positive alpha.',
  'ordered_normal_residue':'P2 du dv ddaux/(3*daux*eaux^6)',
  'rational_quotient':'t=daux^3, eaux^3=G-t',
  'alpha':str(alpha),
  'F':str(F),
  'L':str(L),
  'ell':'log(t/(G-t)); only its rational differential is used.',
  'chain_identity':'alpha dt=d_t F+L*d_t ell',
  'jet_primitive':str(Fd),
  'jet_identity':'D(alpha)dt=d_t[D(F)-L*D(G)/(G-t)]+D(L)*d_t ell, with D(t)=0.',
  'actual_G':str(Ga),'actual_P2':str(P2a),
  'projective_source':'Y0_cubed means Y0^3; the projective degree-nine numerator is Y0^3*(C-2*B^3/(27d)). On Y0=1 it reduces to the affine numerator.',
  'actual_d_jet_primitive':str(Fda),
  'scope':
    'This is an explicit rational-plus-log decomposition of the actual normal residue, '
    'not the unknown Y scalar primitive g0. Multiplying by the first elliptic prefactor '
    'preserves the identity and differentiates that prefactor as well. The coefficient '
    'L=P2/(9G^2) is the original physical source divided by nine, so integrating it or '
    'discarding its logarithmic residue would be circular. The identity alone cannot '
    'replace the missing compatible joint primitive.',
}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
