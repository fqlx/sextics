# Physical cone transitions and the global adjoint jet calculation

This independently confirms reflection_skew's physical finite-flat model
and jet-map calculation. The complete pencil is
used throughout; no genus or bundle claim is made for the normalization of
only the F447/F41 component.

The base is B=P²_Y×P¹_X, with H,L denoting its two hyperplane classes.
Write M=O(15,17), F=O(0,1), and T=O(-2,2). The reduced physical old-coordinate
graph is `d*t_old-n*h²=0`, with d in M and n in M*T=O(13,19), and
`w_old=X2/h` has base weight F. The integral generators
`r=d*w_old,z=d*w_old²` have weights M*F and M*F².
Their quadric has weight M²F² and cubic weight M³F⁶. These two monic equations
give the finite free basis `1,z,z²,r,rz,rz²`; their leading monomials r²,z³
are coprime. The complete intersection is Gorenstein and
`omega_Y=K_B*M³F⁵=O(42,54)`, with character chi¹.

The target chi¹ canonical sections are the constant slot H0(42,54) and
`rz*H0(12,17)`. All six summands of the finite pushforward O_Y have vanishing
H² on B by Kunneth, hence H²(O_Y)=0 for this finite-flat model.

On a good transverse cone component the vertex ideal is
`I=(r,z,d,n)`. Its chi¹ canonical first-jet quotient is
`omega_Y tensor O_B/(d,n)²`; the r,z linear slots have different characters.
This keeps the normal-coordinate action. It does not identify R¹ resolution
pushforward with a direct sum of O_Z bundles killed by I.
For the full pencil complete intersection Z=(d,n), K_Z=O_Z(25,34). The
graded R¹ chi² pieces are therefore O_Z(-17,-20) for the n1 layer and
O_Z(-2,-3),O_Z(-4,-1) for the two n0 slots. The latter also follow independently
from weighted relative adjunction: the actual hol forms h² and t have Hodge
bundle weights O(2,3) and O(4,1), respectively. These formulas concern the
good cone filtration and its physical line transitions; boundary conductor
modifications are not computed.

After twisting the square-ideal resolution by omega_Y, its free generators
have bidegrees (12,20),(14,18),(16,16), and its two syzygies have degrees
(-1,1),(1,-1). The syzygies are completely acyclic, and the generators have
no higher cohomology. Consequently H¹((d,n)² omega_Y)=0 and all these cone
jets interpolate from H0(omega_Y). The target jet-space dimension is45238;
the full chi¹ canonical source has dimension53668. This confirms that the
cone contraction alone does not create a global H20 obstruction.

Crucial scope: additional normalization, conductor, or other boundary adjoint
conditions can restrict the allowed canonical source. They must be imposed
before concluding anything about H20 of the physical degree32 support.
The arithmetic genus9641 in the JSON belongs to the full unsaturated pencil
CI, not the normalization genus of the selected reduced curve. No certificate,
Gysin serving statement, or unrestricted no-go is asserted.

Reproduce the exact line/cohomology calculation with `python compute.py`.
