#!/usr/bin/env python3
"""Exact physical binding and rationalization for the retained Pa residue."""
import json
from pathlib import Path
import sympy as s

r,k,z,lam=s.symbols('r k z lam',nonzero=True)
T=1+z**6
A=1+r*r
B=1+k**6/r**2
iv=4*k*T/(3*z*z)
JJ=k*k*T/A
Delta=3*k**6*z**6-3*k**6-8*r*r*z**6+r*r-k**6*z**6/r**2+2*k**6/r**2
checks={}
def ck(n,v):
    assert s.cancel(v)==0,(n,v)
    checks[n]=True

logh=2*s.log(T)+s.log(A)/2+s.log(B)/2-3*s.log(z)
mat=s.Matrix([[s.diff(iv,t)/iv for t in (r,k,z)],
              [s.diff(JJ,t)/JJ for t in (r,k,z)],
              [s.diff(logh,t) for t in (r,k,z)]])
det=s.factor(mat.det())
ck('physical_log_jacobian',det+2*Delta/(k*r*z*A*B*T))

# On a compatible coefficient-root cover, i0^2=-1, p^2=-T/B,
# j*h=8*k*T^2*B*p/(i0*z^3). Divide by p/i0 for rational checks.
jh_over_p_i=8*k*T*T*B/z**3
coeff=s.factor(iv*jh_over_p_i*det/2)
ck('full_di_dj_dh_coefficient',coeff+32*k*T*T*Delta/(3*r*z**6*A))
ck('plus_pa_residue_density',coeff/6+16*k*T*T*Delta/(9*r*z**6*A))

# Rational Pa sheet. i0=sqrt(-1) is an allowed constant extension.
i0=s.I
ps=(lam-T/lam)/2
ss=(lam*lam+T)/(i0*(lam*lam-T))
ck('physical_pa_conic',ps*ps*(1+ss*ss)+T)
ck('conic_factor_parameter',ps*(1+i0*ss)-lam)

w=z*z
u=JJ/iv**2
N0=9*w*w-16*u*T
L0=256*T**5*N0+729*iv**6*u*w**6
ck('N_boundary_in_physical_coordinates',N0-9*w*w*r*r/A)
ck('L_boundary_in_physical_coordinates',L0-2304*T**5*w*w*r*r*B/A)
ck('right_inverse_denominator',5*u+16-(45*w*w+256*T*A)/(16*T*A))

out={
 'status':'Exact actual finite-residue transport; scalar primitive still open',
 'physical':{'i':str(iv),'J':str(JJ),'Delta':str(Delta),'Pa':'p^2=-T/B'},
 'volume':'di wedge dj wedge dh = -32*k*T^2*Delta*p/(3*i0*r*z^6*A) dr wedge dk wedge dz',
 'plus_pa_residue':'-16*k*T^2*Delta*K*p/(9*r*z^6*A) dr wedge dk wedge dz',
 'root_compatibility':'i0^2=-1, j=k*sqrt(T/A), h=8*T^2*sqrt(A*B)/z^3, p=i0*sqrt(T/B)',
 'rational_pa_chart':{'p':str(ps),'s':str(ss),'r':'k^3/s'},
 'checks':checks,'count':len(checks),
 'limitations':'Rationality does not integrate an arbitrary rational three-form. Full density, residues and K dependence must be retained.'}
p=Path(__file__).with_name('physical-pa-residue-results.json')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':all(checks.values()),'output':str(p)}))
