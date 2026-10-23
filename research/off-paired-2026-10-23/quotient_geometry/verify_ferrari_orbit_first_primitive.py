from pathlib import Path
import json
import sympy as s
S,I,l,W=s.symbols('S I lambda W')
Q=(4*S*S+6*l*S+9*l*l-3*I)/9
R=(I-S*S)/12
m=l-2*S/3
N0=-S*(S+m)**3+2*R*(S+m)**2+8*R**2
N=I**2/18-5*I*S**2/54+I*S*l/9+I*l*l/6-4*S**3*l/9-7*S*S*l*l/6-S*l**3
P=-l*S*S/3-(5*I+33*l*l)*S/48+l*(-I+51*l*l)/64
k=(4*I*I+9*I*l*l+81*l**4)/192
psi=2*W+4*S/3+l
checks={}
checks['source_polynomial_conversion']=s.expand(N-N0)==0
checks['hermite_reduction']=s.expand(N-s.diff(P,S)*Q-P*s.diff(Q,S)/2-k)==0
checks['rational_logarithmic_derivative']=s.factor(3*W*(s.diff(psi,S)+s.diff(psi,W)*s.diff(Q,S)/(2*W))-2*psi)==0
# qSS dS/(3T)=-2N dS/(3D^3W); multiply claimedidentity by3D^3W.
checks['first_primitive_plus_log']=s.expand(-2*N+2*(s.diff(P,S)*Q+P*s.diff(Q,S)/2)+2*k)==0
out={'checks':checks,'status':'Exact coefficient-orbit first primitive and rational dlog correction; physical-density correction remains.'}
assert all(checks.values()),checks
Path(__file__).with_name('ferrari-orbit-first-primitive-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
