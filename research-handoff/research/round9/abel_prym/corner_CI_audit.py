"""Exact QQ(zeta) quasismooth witness and Hilbert-character audit for the corner CI."""
from pathlib import Path
import sympy as s,json,time
HERE=Path(__file__).parent;start=time.monotonic()
p=json.load(open(HERE.parent.parent/'round10'/'horizontal5'/'fresh'/'boundary'/'blowup_quadratic.json'))
v,zz=s.symbols('v zeta');loc={'v':v,'zeta':zz};A,C,D,B,E=[s.sympify(p[k],locals=loc)for k in('A','C','D','B','E')]
lam=s.Rational(5,7)*zz
q2=lam*(B-A*lam);q1=B*(C*lam+E)-2*A*E*lam;q0=-D*B*B+B*C*E-A*E*E
conditions={'A':A,'B':B,'D':D,'quadric_pencil_leading':q2,'quadric_pencil_constant':q0,'quadric_pencil_discriminant':q1*q1-4*q2*q0,'T0_transverse':C*C-4*A*D,'U0_transverse':(E-C*lam)**2-4*D*(A*lam*lam-B*lam)}
records={}
for name,phi in [('order4',zz**2+1),('order12',zz**4-zz**2+1)]:
 checks={}
 for key,f in conditions.items():
  rr=s.rem(s.Poly(s.expand(f.subs(v,2)),zz),s.Poly(phi,zz)).as_expr()
  assert rr!=0,(name,key)
  nn=s.resultant(phi,rr,zz);assert nn!=0
  checks[key]={'nonzero_exact':True,'norm_numerator_bits':int(abs(s.numer(nn))).bit_length(),'remainder_degree':int(s.degree(rr,zz))}
 records[name]=checks
# Below defining degree12 the Hilbert function is just the ambient monomial count.
mon=[]
for eps in range(3):
 for W in range(4):
  for b in range(2):
   for r in range(2):
    degree=3*eps+2*W+6*b+6*r
    if degree<=7:mon.append({'exponents_eps_W_b_r':[eps,W,b,r],'degree':degree,'dualizing_character':(W+1)%3,'H1O_character':(-W-1)%3})
assert len(mon)==10
counts=[sum(m['H1O_character']==i for m in mon)for i in range(3)];assert counts==[2,2,6]
result={'leading_equations':'F0=W6+b*(r+(5/7)*zeta*eps²), D0=A*r²+C*b*r+D*b²+eps²*(B*r+E*b), r=(a6+1)/b in the packet convention.','weights_eps_W_b_r':[3,2,6,6],'degrees':[12,12],'a_invariant':7,'two_quadric_model':'T=eps²,U=W³: E⊂P3(U,b,r,T), U²+b*(r+lambda*T)=0, A*r²+Cbr+D*b²+T*(Br+Eb)=0.','quadric_pencil':'det(M_D+t*M_F)=t*(q2*t²+q1*t+q0)/4, up to a fixed sign; fourth root is infinity, simple when q2!=0.','quasismooth_reason':'Smooth quadric intersection plus transverse divisors T0 and U0, with their intersection empty, makes the affine (2,3)-root pullback smooth off the origin. All conditions hold exactly over both cyclotomic fields at v=2, hence generically.','exact_generic_witnesses':records,'coarse_exceptional_curve':'A smooth genus1 intersection of quadrics; the weighted projective coarse curve is this E. mu3(W) acts trivially on E; nontrivial pg characters come from thickenings/orbifold layers.','monomials_degree_le7':mon,'geometric_genus':10,'H1O_resolution_char_counts':counts,'scope':'Exact generic local isolated-ICIS and Hilbert/local-duality character calculation. Global compactification, gluing of local defects, and source projection remain separate.','seconds':time.monotonic()-start}
(HERE/'corner_CI_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
