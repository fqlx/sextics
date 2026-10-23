from pathlib import Path
import json
import sympy as s
u,z,a,b,e,S=s.symbols('u z a b e S')
p=a*b
f=z/s.Integer(2)+p/3
H=1+z**6+a**6+b**6+u*f
Z=b**6-a**6
Ephys=z*p/2
U=-S*e/(12*u**2)
E=(4*u**6-S**2+S*e**2/4)/u**3
P=2*E/z
G=3*e*u**3-f*U-u*P/3
MA=(6*b**5*P-a*G)/(6*Z)
MB=(b*G-6*a**5*P)/(6*Z)
checks={}
checks['lift_product']=s.factor(b*MA+a*MB-P)==0
checks['lift_sum_sixth']=s.factor(6*a**5*MA+6*b**5*MB-G)==0
checks['lift_S']=s.factor(s.diff(H,u)*U+s.diff(H,a)*MA+s.diff(H,b)*MB-3*e*u**3)==0
checks['physical_coefficient_jacobian']=s.factor(s.det(s.Matrix([[s.diff(Ephys,a),s.diff(Ephys,b)],[s.diff(H,a),s.diff(H,b)]]))-3*z*Z)==0
# Compute the original-coordinate divergence after imposing the physical S,e.
sub={S:H,e:Ephys}
cur=[s.cancel(t.subs(sub, simultaneous=True)) for t in [U,MA,MB]]
direct=sum(s.diff(t,x) for t,x in zip(cur,[u,a,b]))
expected=(2*S*e/(3*u**3)-((a**6+b**6)*G-12*p**5*P)/Z**2).subs(sub, simultaneous=True)
checks['physical_divergence_direct']=s.factor(direct-expected)==0
out={'checks':checks,'status':'Exact physical lift and divergence; no primitive.'}
assert all(checks.values()),checks
Path(__file__).with_name('ferrari-physical-mobius-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
