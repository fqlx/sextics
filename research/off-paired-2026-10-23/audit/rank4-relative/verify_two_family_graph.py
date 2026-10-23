"""Target-bound legality and relative maps of the source-guided graph.

These are necessary interface identities, not a current or certificate.
"""
import json
from pathlib import Path
import sympy as s

w,x,y,z,u,v=s.symbols('w x y z u v')
H=w**6+x**6+y**6+z**6+w**3*x*y*z/2
D=H-w**6-z**6
C=x**3*z/2+w**2*x*y/3
Cb=-w**3*z/2
G=s.expand(8*D**2*C**3+w**9*z**3*H**2)
assert {sum(mon) for mon,coef in s.Poly(G,w,x,y,z).terms()}=={24}
assert G.subs({w:1,z:1,x:0,y:0})==4
F=H+u**6+v**6+C*u*v
assert s.Poly(F,u).LC()==1
assert not G.has(u,v)

# In the universal parameter ring the graph is C^3 D^2=Cb^3 H^2.
# The explicit rational scale r=(H/D)/(C/Cb) works without extracting roots.
HH,DD,CC,BB,r,q,Z=s.symbols('HH DD CC BB r q Z')
graph=CC**3*DD**2-BB**3*HH**2
scale=HH*BB/(DD*CC)
assert s.cancel(scale**2-CC/BB+graph/(BB*CC**2*DD**2))==0
assert s.cancel(scale**3-HH/DD+HH*graph/(CC**3*DD**3))==0
ep=(HH+CC*r*q)**2-4*r**6*q**6
bg=(DD+BB*q)**2-4*q**6
assert s.expand(ep.subs({HH:r**3*DD,CC:r**2*BB})-r**6*bg)==0
Delta=lambda h,c:4*c**6-729*h**4
assert s.expand(Delta(r**3*DD,r**2*BB)-r**12*Delta(DD,BB))==0
assert s.expand(graph.subs({HH:H,DD:D,CC:C,BB:Cb})-G/8)==0
for j in (0,1,2,3,4):
    assert s.cancel((r*q)**j*r/(r**3*Z)-r**(j-2)*q**j/Z)==0
    assert s.cancel((r*q)**j*q/(r**3*Z)-r**(j-3)*q**(j+1)/Z)==0

out={'status':'passed','exact_groups':8,
     'scope':'Degree24 nonzero background support, monic-endpoint coprimality interface, rational genus2 isomorphism and discriminant scaling; no primitive or source match.',
     'relative_basis':'pullback omega_j(endpoint)=r^(j-2) Omega_j(background), at fixed r',
     'horizontal_warning':'With dr retained, p^j dp/Zp=r^(j-2)q^j dq/wb+r^(j-3)q^(j+1)dr/wb.',
     'r_on_homogeneous_graph':'-H*w^3*z/(2*C*D)'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
