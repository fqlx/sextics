"""Independent Fraction substitutions for the source normal-constraint identity."""
from fractions import Fraction as F
from pathlib import Path
import json

samples = [(F(1),F(0),F(1)),(F(1),F(1),F(1)),(F(2),F(1),F(3)),
           (F(1,2),F(-1),F(2,3)),(F(-2),F(3,2),F(-1)),
           (F(3),F(-2,3),F(1,3)),(F(4,3),F(2,5),F(-3,2)),
           (F(-1,2),F(7,3),F(5,4)),(F(5),F(-1,7),F(2)),
           (F(2,7),F(1,5),F(3,11))]

for a,z,C in samples:
    q=3*C-F(3,2)*a*z
    H=a*a+q**6/a**2+z**6+q*z/2+1
    Ha=2*a-2*q**6/a**3-9*z*q**5/a**2-F(3,4)*z*z
    Hz=6*z**5+q/2-F(3,4)*a*z-9*q**5/a
    L=z/a+F(2,9)*q/a**2
    K=3*a*z+12*z**5
    M=-18*a**3+54*a*z**6
    Q=q*q+K*q+M
    E=F(1,2)-9*(K**4-3*K*K*M+M*M)/a
    F0=6*z**5-F(3,4)*a*z-9*(K**3*M-2*K*M*M)/a
    J5=-9*(q**3-K*q*q+(K*K-M)*q-K**3+2*K*M)/a
    assert Ha-L*Hz == -Q/(9*a*a)
    assert Hz == J5*Q+E*q+F0
    R0=F0**2-K*E*F0+M*E*E
    assert R0
    w1=(-F0*(K*K-M)+K*M*E)/(6*a*a*R0)
    w0=M*(E*M-K*F0)/(6*a*a*R0)
    Wb=w1*q+w0
    V=(K-q)/(6*a*a)-E*w1-J5*Wb
    U0=-9*a*a*V
    W0=Wb+9*a*a*L*V
    assert Ha*U0+Hz*W0 == -q**3/(6*a*a)

result={"status":"passed","exact_fraction_groups":len(samples),
        "scope":"Substitution checks of the physical normal constraint, not a full primitive or a substitute for generic polynomial identities."}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
