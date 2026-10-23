"""Exact ambient lift of a rational endpoint current.

This is extraction infrastructure, NOT a certificate for the off-paired source.
It handles every hyperelliptic-odd rational current, including higher p and Z
poles: replace Z**2 by f in its rational coefficient functions first.
"""
from pathlib import Path
import json
import sympy as s

e,b,H,C,A,dq=s.symbols('e b H C A dq')
p=e*b
R=e**6+b**6
Z=e**6-b**6
L=H+C*p
F=R+L
f=L**2-4*p**6
qh=s.Function('qh')(p)
qc=s.Function('qc')(p)
ss=s.Function('s')(p)
pp=s.symbols('pp')
sp=s.diff(s.Function('s')(pp),pp).subs(pp,p)
M=A-6*qh-6*p*qc
Scrit=3*R+C*p
K=M+6*ss*Scrit/p
ve=-3*ss*e/p+K*e/(6*Z)
vb=-3*ss*b/p-K*b/(6*Z)
divv=6*dq+s.diff(ve,e)+s.diff(vb,b)
E=f*(dq-sp)-L*(qh+p*qc)+ss*(C*L-12*p**5)+A*L/6
Qstar=(6*(R-L)*(dq-sp)-M-6*ss*C)/Z**2

# qh = q_vector(H), qc = q_vector(C); the other three components are
# v_base=6*q_vector.  This verifies the ambient normal equation literally.
normal=6*(qh+p*qc)+(6*e**5+C*b)*ve+(6*b**5+C*e)*vb
checks={
 'actual_ambient_normal_is_A':s.cancel(normal-A)==0,
 'literal_ambient_divergence_vs_complete_current':s.simplify(divv-6*E/Z**2-F*Qstar)==0,
}
assert all(checks.values()),checks
out={
 'status':'GENERAL_EXACT_CURRENT_TO_AMBIENT_CERTIFICATE_LIFT; TARGET_CURRENT_STILL_OPEN',
 'checks':checks,
 'source':'A=y^3 on X0=1, H=1+x^6+y^6+z^6+xyz/2, C=x^3*z/2+xy/3',
 'current':'J=q2(x,y,z,p) wedge dp/Z + s(x,y,z,p)*dxdy dz/Z; q_vector=(q_yz,-q_xz,q_xy)',
 'complete_obstruction':'E=f*(div(q_vector)-partial_p(s))-L*(q_vector(H)+p*q_vector(C))+s*(C*L-12p^5)+A*L/6',
 'notation':'p=e*b, R=e^6+b^6, Z=e^6-b^6, L=H+Cp, F=R+L, f=L^2-4p^6',
 'vector':{
  'base':'v_base=6*q_vector',
  'M':'A-6*q_vector(H)-6*p*q_vector(C)',
  'K':'M+6*s*(3R+Cp)/p',
  'v_e':'-3*s*e/p+K*e/(6Z)',
  'v_b':'-3*s*b/p-K*b/(6Z)',
 },
 'exact_ambient_identities':[
  'dF(v)=A exactly, before restriction to F=0',
  'div(v)=6E/Z^2+F*[6*(R-L)*(div(q_vector)-partial_p(s))-M-6sC]/Z^2',
  'A-dF(v)+F*div(v)=6F*E/Z^2+F^2*Qstar',
 ],
 'closure_requirement':'Only E=0 yields a certificate. No current in the present work has yet passed this test.',
 'homogeneous_export':'Set v_X0=0 and homogenize affine v_i to degree1 using X0. Clear a common denominator D and homogenize D,N_i to degrees d,d+1. Verify complex coprimality and the cleared identity before Lean submission.',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'exact general ambient-lift identities; target remains UNSOLVED')
