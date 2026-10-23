# A rational degree-six cover with constant actual density

This is an exact coordinate and source simplification. It supplies no
primitive or certificate.

Fix a constant field k of characteristic zero, taking k=C for the full
certificate contract. Start with the physical G36 cubic-ray chart

    f=H+Bp+Cp^3,
    H=1+z^2+t,
    B=U/2+K/3+zUK/2,
    C=z^-2+U^6+K^6/t,
    Omega=dz dU dK dt/(18tz^2),
    R=Bp/(B+3Cp^2)^3.

Adjoin h with h^6=t and set

    Z=1/z, u=U, v=K/h.

The new base k(Z,h,u,v) is rational and has degree six over the G36 base.
The exact physical equation and source become

    H=1+Z^-2+h^6,
    C=Z^2+u^6+v^6,
    B=u/2+hv/3+huv/(2Z),
    f=H+Bp+Cp^3,
    Omega=-(1/3) dZ dh du dv,
    source=-(R/3) dZ dh du dv.

The factor -1/3 is the actual Jacobian. The cubic variable p has not
changed. In particular the complete canonical two-current system uses
ordinary divergence in these four coordinates. Its source is still
(0,1/(HC)) relative to the displayed Omega.

With the exact rational symplectic form

    omega0=dZ dh+du dv,

its Hamiltonians preserve the actual volume, which is the constant multiple
-omega0^2/6. The coefficient brackets are

    {H,C}=-12Zh^5,
    {H,B}=-2v/(3Z^3)-uv/Z^4+3h^6uv/Z^2,
    {B,C}=-2Zv/3-uv+3v^5+3hv^6/Z-2hu^5-3hu^6/Z.

The first bracket is one monomial. Every physical derivative of the full
H,B,C must still be retained in a proposed current.

Over k=C, the six deck transformations act by

    h -> zeta6*h, v -> zeta6^-1*v, Z,u,p fixed.

They preserve H,B,C,dh dv and the complete physical source. A completed
rational primitive on this cover therefore descends by normalized field
trace. Trace commutes with exterior differentiation. This statement concerns
the fixed constant field k; it does not descend complex constants to Q.

Conversely every source primitive on G36 pulls back to this cover. Combining
this trace with the previously checked cubic-ray/G36 residue and Piola
transport gives the conditional route back to a homogeneous legal witness for
the immutable original target. The existing transport still has to be applied
to any completed current; no witness has been found here.

`constant_density_chart.py` verifies eleven exact coordinate, bracket and
deck checks. The optional one-angle CM normalization in `../horizontal-cm/`
is a further finite change; no CM roots are needed for this entry chart.
