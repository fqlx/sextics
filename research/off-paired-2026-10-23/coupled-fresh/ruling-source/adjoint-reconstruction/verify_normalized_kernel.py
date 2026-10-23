"""Exact normalized-moduli/Jacobian check for the actual outer-E kernel.

No source solution is asserted.  The checks establish a complete integrating
factor for the infinity condition in the stated single-annihilator channel.
"""
import importlib.util
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('physical_source_adjoints',HERE.parent/'physical_source_adjoints.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
R,S,z,k=p.R,p.S,p.z,p.k
A=1+R;B=1+S;T=1+z**6
delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
lc=[1/(6*R)-1/(3*A),1/(6*S)-1/(3*B),-2*z**5/T]
ld=[1/(6*R)-2/(3*A),1/(6*S)-1/(6*B),1/z-z**5/T]
le=[-1/(6*A),-1/(6*B),1/z-4*z**5/T]
logs=s.Matrix([lc,ld,le])
checks=[]
def check(name,value):
    reduced=s.factor(value)
    assert reduced==0,(name,reduced)
    checks.append(name)
check('log-coordinate determinant',logs.det()-delta/(36*R*S*z*A*B*T))
def apply_logs(V,values):return V['R']*values[0]+V['S']*values[1]+V['z']*values[2]
check('E fixes normalized c',apply_logs(p.LE,lc))
check('E fixes normalized d',apply_logs(p.LE,ld))
check('E changes normalized e by e/E',apply_logs(p.LE,le)-2/z)

# eta_b = L eta_norm and normalized coefficient e_E=s_e.
logL=[-1/(6*A),-s.Rational(2,3)/B,-z**5/T]
check('physical eta_b character',apply_logs(p.LE,logL)-p.char(p.LE))

# Hsrc=4*T^(4/3)*A^(11/6)*B^(5/6)/(z*k*delta).
# All logarithmic derivatives are rational; no actual log is used.
logH_R=s.Rational(11,6)/A-1/(6*R)-s.diff(delta,R)/delta
logH_S=s.Rational(5,6)/B-1/(6*S)-s.diff(delta,S)/delta
logH_z=8*z**5/T-1/z-s.diff(delta,z)/delta
logH=[logH_R,logH_S,logH_z]
check('infinity equation integrating factor',p.hE-apply_logs(p.LE,logH))

# The exact exponent bookkeeping for Hsrc = mu/(Jac cde) * L * s_e.
# Entries: T,A,B,k,z,delta,constant.  mu=(1/108) k^-5 and
# detJac=(z*k^2*delta/(432*R*S))*T^-13/6*A^-13/6*B^-5/3.
# R*S=k^6 has already been substituted in the determinant exponent.
j_exponents=[-s.Rational(13,6),-s.Rational(13,6),-s.Rational(5,3),-4,1,1]
mu_exponents=[0,0,0,-5,0,0]
L_exponents=[-s.Rational(1,6),-s.Rational(1,6),-s.Rational(2,3),0,0,0]
se_exponents=[-s.Rational(2,3),-s.Rational(1,6),-s.Rational(1,6),0,0,0]
computed=[m-j+l+e for m,j,l,e in zip(mu_exponents,j_exponents,L_exponents,se_exponents)]
assert computed==[s.Rational(4,3),s.Rational(11,6),s.Rational(5,6),-1,-1,-1]
checks.append('complete normalized source density exponents')

out={'status':'exact integrating factor, not a source solution','checks':checks,
     'normalized_moduli':{'c':'C*T^(-1/3)*(A*B)^(-1/3)',
                          'd':'D*T^(-1/6)*A^(-2/3)*B^(-1/6)',
                          'e':'E*T^(-2/3)*(A*B)^(-1/6)'},
     'Hsrc':'4*T^(4/3)*A^(11/6)*B^(5/6)/(z*k*delta)',
     'kernel':'u=Hsrc^(-1)*W(c,d) solves V_E(u)+hE*u=0',
     'remaining_equation':'D_S(V_T(u)+hT*u)=D_S(hT), with weighted D_S',
     'certificate':False}
(HERE/'normalized-kernel-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact normalized-coordinate, character and kernel checks')
