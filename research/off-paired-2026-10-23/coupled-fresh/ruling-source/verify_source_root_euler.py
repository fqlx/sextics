"""Exact sparse inverse-root moment identities; logarithmic defect retained."""
import json
from pathlib import Path
import sympy as s
I,u,w=s.symbols('I u w',nonzero=True)
T=1+w**3;N0=9*w*w-16*u*T
v=s.factor(64*u*w*T*T*N0/(9*(256*T**5*N0+729*I**6*u*w**6)))
E0w=s.factor(-I*s.diff(v,I)/s.diff(v,w))
J=u*I**2;k=3*I*w/(4*T);A=k*k*T/J;R=A-1;S=k**6/R
Delta=3*R*S*w**3-3*R*S-8*R*w**3+R-S*w**3+2*S
h=s.factor(3*I*w**3/(32*J*T*T*Delta))
rhs=s.factor(64/(729*u)*I**-7*T**3/w**4*E0w)
rat=-1/(3*w**3)+w**3+w**6/6
checks={
 'actual_source_Euler_moment':s.factor(h-rhs)==0,
 'rational_moment_plus_log_derivative':s.factor(s.diff(rat,w)+3/w-T**3/w**4)==0,
 'linear_i6_root_equation':s.factor(I**6-64*N0*T*T*(u*w-36*v*T**3)/(6561*u*v*w**6))==0,
}
assert all(checks.values())
out={'checks':checks,'status':'passed','source':'hsrc=(64/(729u))i^-7(T³/w⁴) E0(w), u=J/i²,E0=i partial_i+2J partial_J at fixedv',
     'rational_moment':str(rat),'retained_logarithmic_moment':'3 log(w)',
     'scope':'exact source factorization; logarithmic coefficients are not valid rational current potentials unless explicitly canceled; no primitive claimed'}
Path(__file__).with_name('source-root-euler-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
