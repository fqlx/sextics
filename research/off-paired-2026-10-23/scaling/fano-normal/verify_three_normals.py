#!/usr/bin/env python3
"""The exact physical source in three Fano/Cardano normal coordinates."""
import sympy as s
import json
S,T,c,H,B,C,Hi,Bi,Ci=s.symbols('S T c H B C Hi Bi Ci',nonzero=True)
G=s.Matrix([S**3+T**3-H,c**3-C,B+3*c*S*T])
J=s.factor(G.jacobian([S,T,c]).det())
L=S*S+S*T+T*T
delta=S**3-T**3
p=-(S+T)/c
sub={H:S**3+T**3,B:-3*c*S*T,C:c**3}
g=(B+3*C*p*p).subs(sub)
R=s.factor((B*p/(B+3*C*p*p)**3).subs(sub))
N=-3*S*T*(S*S-T*T)/L**2
ci=Ci/(3*c*c)
ui=-Bi/(3*c)-S*T*Ci/(3*c**3)
si=(S*Hi/3-T*T*ui)/delta
ti=(S*S*ui-T*Hi/3)/delta
checks={
 'physical_cubic':s.factor((H+B*p+C*p**3).subs(sub))==0,
 'normal_jacobian':s.factor(J+27*c**3*delta)==0,
 'normal_g':s.factor(g-3*c*L)==0,
 'actual_source':s.factor(R-S*T*(S+T)/(9*c**3*L**3))==0,
 'three_normal_numerator':s.factor(N-J*R)==0,
 'base_G1_derivative':s.factor(3*S*S*si+3*T*T*ti-Hi)==0,
 'base_G2_derivative':s.factor(3*c*c*ci-Ci)==0,
 'base_G3_derivative':s.factor(Bi+3*ci*S*T+3*c*T*si+3*c*S*ti)==0,
 'W_H_tangent_Q_derivative':s.factor(3*c*T+3*c*S*(-S*S/(T*T))+3*c*delta/(T*T))==0,
}
qE=-(S+T)/(2*L)
deltaE=lambda a:3*T*T*s.diff(a,S)-3*S*S*s.diff(a,T)
checks['elliptic_primitive']=s.factor(deltaE(qE)-N)==0
checks['coupling_derivative']=s.factor(deltaE(B+3*c*S*T)+9*c*delta)==0
checks['double_Q_scalar']=s.factor(
    s.diff(qE*deltaE(B+3*c*S*T)/(3*S*T*(c**3-C)),c)/(3*S*T)
    -qE*delta*(2*c**3+C)/(S*S*T*T*(c**3-C)**2))==0
tt=s.symbols('tt',nonzero=True)
Deff=B**3/(27*tt**3)
checks['second_source_parameter_derivative']=s.factor(
    (C-2*Deff)/(C+Deff)**2
    +tt**2*s.diff(1/(tt*(C+Deff)),tt))==0
assert all(checks.values()), checks
print(json.dumps({'all_passed':True,'checks':checks,'J':str(J),'R':str(R),'N':str(N)},indent=2))
