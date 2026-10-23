"""Exact transverse integral model at N0=N1=0 on the marked graph.

The local geometric interpretation requires a transverse common-zero curve,
regular canonical parameters, and a smooth genus4 curve there.  It does not
assert global H20 or a serving Gysin class.
"""
from pathlib import Path
import sympy as s
import json,pickle
HERE=Path(__file__).parent
Z,R,U,V,w,L,r,x,c=s.symbols('Z R U V w L r x c')
Q=Z*U-R*R
C0=L*U**3+r*U*U*V+V**3/x
G=Z**3+c*R**3+c*Z*R*V+C0
Gred=Z**3+c*Z*R*(U+V)+C0
assert s.expand(G-Gred+c*R*Q)==0
curve=w**6+c*(1+V/U)*w**3+L+r*V/U+(V/U)**3/x
assert s.cancel(G.subs({Z:U*w*w,R:U*w})-U**3*curve)==0
assert s.expand(Q.subs({Z:U*w*w,R:U*w}))==0

# The two integral generators give a finite monic model, not only a
# rational parametrization of the blowup.  The basis below has six elements.
norm=(Z**3+C0)**2-c*c*Z**3*U*(U+V)**2
identity=s.expand(norm-Gred*(Z**3+C0-c*Z*R*(U+V)))
assert s.expand(identity-c*c*Z*Z*(U+V)**2*(R*R-Z*U))==0
assert s.degree(norm,Z)==6 and s.Poly(norm,Z).LC()==1

# A concrete physical smooth-curve witness is checked separately in
# transverse_point.py using the previously audited D1,D2 discriminants.
# Character counts in canonical sections follow from the equivariant
# adjunction factor det(coords)/(chi(Q)*chi(G))=chi.
coordinate_characters=[2,1,0,0]
canonical_shift=(sum(coordinate_characters)-2-0)%3
hol1=[(ch+canonical_shift)%3 for ch in coordinate_characters]
H1O=[(-ch)%3 for ch in hol1]
H1O1=[(-canonical_shift)%3]
counts=lambda xs:[xs.count(j) for j in range(3)]
assert counts(hol1)==[1,2,1]
assert counts(H1O)==[1,1,2]
assert counts(H1O+H1O1)==[1,1,3]

packet=dict(symbols=(Z,R,U,V,w,L,r,x,c),quadric=Q,cubic=G,
            reduced_cubic=Gred,monic_Z_relation=s.expand(norm),
            integral_map={'Z':U*w*w,'R':U*w,'U':'N0','V':'N1'},
            generic_inverse='w=R/U; s=V/U',
            finite_module_basis=(s.Integer(1),Z,Z*Z,R,Z*R,Z*Z*R),
            characters=dict(coordinates=coordinate_characters,quadric=2,cubic=0,
                            canonical_shift=canonical_shift,H0K=counts(hol1),
                            H1O=counts(H1O),H1O1=counts(H1O1),R1O=counts(H1O+H1O1)))
(HERE/'canonical_cone.pickle').write_bytes(pickle.dumps(packet))
report=dict(all_algebraic_identities_exact=True,
            canonical_model='ZU=R²; Z³+cR³+cZRV+LU³+rU²V+V³/x=0',
            finite_degree=6,genus=4,canonical='K_C=O_C(1) as ordinary line bundles',
            resolution='Blow up the vertex; exceptional C, conormal O_C(1)=K_C',
            transverse_geometric_genus=5,
            formal_functions_reason='h1(O_C)=4, h1(O_C(1))=1, h1(O_C(n))=0 for n>=2. The connecting map from constants at the first thickening is zero because 1 lifts.',
            equivariant_canonical='K_C=O_C(1) tensor chi under w -> zeta*w',
            H0K_characters=counts(hol1),H1O_characters=counts(H1O),
            H1O1_characters=counts(H1O1),R1O_characters=counts(H1O+H1O1),
            necessary_local_hypotheses=['N0,N1 transverse along a common-zero curve',
                'x and all parameter/frame denominators are units',
                'the genus4 projective curve is smooth (D1*D2 nonzero)'],
            global_obligation='Determine the resulting coherent R1 sheaf along the physical base curve, its transitions/linearizations, and the global connecting map H1(R1) -> H3(O_normalization). Nonzero exceptional surface pg does not imply a global H20 class.',
            scope='Exact local integral model and conditional transverse singularity/Hodge-character calculation; no global serving statement or certificate.')
(HERE/'canonical_cone.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
