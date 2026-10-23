"""Exact normalized-moduli source density and outer-E adjoint identities."""
import json
from pathlib import Path
import sympy as s

R,S,z,k=s.symbols('R S z k',nonzero=True)
A,B,T=1+R,1+S,1+z**6
Delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
checks=[]
def check(name,expr):
    assert s.factor(expr)==0,(name,s.factor(expr))
    checks.append(name)

# Rows are rational logarithmic derivatives, so fractional-power branches
# are never evaluated or silently replaced.
lc=s.Matrix([[1/(6*R)-1/(3*A),1/(6*S)-1/(3*B),-2*z**5/T],
             [1/(6*R)-2/(3*A),1/(6*S)-1/(6*B),1/z-z**5/T],
             [-1/(6*A),-1/(6*B),1/z-4*z**5/T]])
check('normalized_log_jacobian',lc.det()-Delta/(36*R*S*z*A*B*T))
check('actual_density_r_k_to_R_S',k/(108*R*S)-1/(108*k**5)*k**6/(R*S))

# Sixth powers give an exact source-density identity under k^6=RS.
cde6=(z**2*k**2/12)**6/(T**7*A**7*B**4)
Lep6=1/(T**5*A**2*B**5)
mu6=1/(108**6*k**30)
jlog6=(Delta/(36*R*S*z*A*B*T))**6
H6=4**6*T**8*A**11*B**5/(z**6*k**6*Delta**6)
num=s.together(mu6*Lep6/(cde6*jlog6)-H6).as_numer_denom()[0]
check('full_source_density_sixth_power',s.rem(num,s.Poly(k**6-R*S,k),k))

# Independent explicit coefficient lift of partial_E.
t=6*z**6/T
ca,cz=2-1/R-3/S,-6+4/R+2/S
relative_E=2/z
constant=relative_E*(-2*(1+1/R)-4*(1+1/S)+12)
Z=s.factor(-constant/(ca*t+cz))
alpha=s.factor(t*Z)
v=s.factor(s.Rational(3,2)*(alpha-Z+relative_E))
u=s.factor(-Z-v/3)
VR=s.factor(A*(alpha-2*u-2*v))
VS=s.factor(B*(alpha+2*u-2*v))
Vz=s.factor(z*Z)
V=s.Matrix([VR,VS,Vz])
check('outer_E_fixes_normalized_c',(lc*V)[0])
check('outer_E_fixes_normalized_d',(lc*V)[1])
check('outer_E_normalized_e_velocity',(lc*V)[2]-relative_E)

div=s.diff(VR,R)+s.diff(VS,S)+s.diff(Vz,z)-s.Rational(5,6)*(VR/R+VS/S)
ceta=-alpha-u+s.Rational(5,3)*v
hE=s.factor(div+ceta)
logw=s.Matrix([1/(6*R)+s.diff(Delta,R)/Delta-s.Rational(11,6)/A,
               1/(6*S)+s.diff(Delta,S)/Delta-s.Rational(5,6)/B,
               1/z+s.diff(Delta,z)/Delta-8*z**5/T])
check('outer_E_adjoint_integrating_factor',V.dot(logw)+hE)
out={'status':'passed','checks':checks,'count':len(checks),
     'source_density':'H=4 T^(4/3)A^(11/6)B^(5/6)/(z k Delta)',
     'outer_E_adjoint_kernel':'w=H^(-1) W(c,d)',
     'scope':'Exact coordinate/source and one adjoint constraint only; remaining normal-function and infinity equations unsolved.',
     'certificate':False}
Path(__file__).with_name('normalized-moduli-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
