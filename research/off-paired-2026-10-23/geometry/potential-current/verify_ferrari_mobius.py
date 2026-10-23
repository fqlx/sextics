from pathlib import Path
import json
import sympy as s
q,S,R,T=s.symbols('q S R T')
P=q**6+2*S*q**4+(S**2-4*R)*q**2-T**2
M0=lambda f:3*T*s.diff(f,S)+(4*R-S**2)*s.diff(f,T)-S*T*s.diff(f,R)/2
Mq=-T/q
M=lambda f:s.cancel(M0(f)+Mq*s.diff(f,q))
E=lambda f:2*S*s.diff(f,S)+3*T*s.diff(f,T)+4*R*s.diff(f,R)
def zero_mod(f):
 n=s.together(f).as_numer_denom()[0]
 return s.rem(n,P,q).expand()==0
qs=-s.diff(P,S)/s.diff(P,q)
qr=-s.diff(P,R)/s.diff(P,q)
qt=-s.diff(P,T)/s.diff(P,q)
I=S**2+12*R
J=72*S*R-27*T**2-2*S**3
checks={
 'M_tangent_pair_polynomial':s.expand(M(P))==0,
 'zero_coefficient_divergence':s.diff(3*T,S)+s.diff(4*R-S**2,T)+s.diff(-S*T/2,R)==0,
 'M_q3':s.cancel(M(q**3)+3*T*q)==0,
 'M_q5':s.cancel(M(q**5)+5*T*q**3)==0,
 'M2_q':zero_mod(M(Mq)+q**3+2*S*q),
 'M3_q':zero_mod(M(-q**3-2*S*q)+2*S*Mq+3*T*q),
 'M_qS':zero_mod(M(qs)-T*qs/q**2-2*S*qt-T*qr/2),
 'I_invariant':s.expand(M0(I))==0,
 'J_invariant':s.expand(M0(J))==0,
 'elliptic_orbit':s.expand(27*T**2-6*I*S+8*S**3+J)==0,
 'shifted_Euler_fixes_R':s.cancel(M0(R)+S*T*E(R)/(8*R))==0,
 'shifted_Euler_fixes_j':s.cancel(M0(J**2/I**3)+S*T*E(J**2/I**3)/(8*R))==0,
}
assert all(checks.values()),checks
out={'convention':'G=v4+S v2+T v+R; R constant, T linear','checks':checks,'status':'Exact covariant identities only; no physical current or certificate.'}
Path(__file__).with_name('ferrari-mobius-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
