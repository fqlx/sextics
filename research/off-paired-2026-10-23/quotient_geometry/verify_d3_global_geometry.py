from pathlib import Path
import json
import sympy as s
r,ss,l,m,a,b,q=s.symbols('r s lambda mu a b q')
X0=r*l;X1=ss*l;X2=a;Y0=3*ss**2*m;Y1=-2*r*r*m;Y2=b
D3=3*X1**2*Y1+2*X0**2*Y0
F=sum(x**6 for x in [X0,X1,X2,Y0,Y1,Y2])+X0**3*X1*Y0*Y1/2+X1**3*X2*Y1*Y2/2+X0**2*X1*X2*Y0*Y2/3
Z=a**6+b**6+(r**6+ss**6)*l**6+(729*ss**12+64*r**12)*m**6-3*r**5*ss**3*l**4*m**2
A=q**6+1;B=729+64*q**12;DD=-3*q**5;C=s.expand(A*A*B-4*q**15)
L=s.symbols('L')
checks={'support_pullback':s.expand(D3)==0,'sextic_pullback':s.expand(F-Z)==0,'cubic_discriminant':s.factor(s.discriminant(A*L**3+DD*L**2+B,L)+27*B*C)==0}
for name,P in [('A',A),('B',B),('C',C)]:checks[name+'_squarefree']=s.gcd(P,s.diff(P,q))==1
for name,P,Q in [('AB',A,B),('AC',A,C),('BC',B,C)]:checks[name+'_coprime']=s.gcd(P,Q)==1
# Degrees of [Sym^2 E^* tensor O(3)]^* for E^*=(1,2,0,0).
deg=[-(3+d+e) for i,d in enumerate([1,2,0,0]) for e in [1,2,0,0][i:]]
checks['relative_dual_all_negative']=all(d<0 for d in deg)
out={'checks':checks,'relative_dual_degrees':deg,'status':'Exact polynomial checks for smooth bundle resolution; H20=0 follows from the stated relative Serre-duality argument. No certificate.'}
assert all(checks.values()),checks
Path(__file__).with_name('d3-global-geometry-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
