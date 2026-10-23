# A finite global adjoint computation: what it would have to compute

This is a precise reduction, not a completed computation.

Let X be a projective compactification of the **correct saturated main
component** of the moving-j0 slope surface, including the intrinsic double
cover U²=s/v. Let pi:S -> X be a resolution through normalization. In
characteristic zero the Grauert--Riemenschneider vanishing theorem, applied
after normalization and then pushed along its finite map, gives

    H¹(S,omega_S) = H¹(X,pi_*omega_S).

The U->-U odd part is dual to the desired odd global holomorphic one-forms.
If X is Gorenstein, write pi_*omega_S=Adj_X * omega_X. Then the problem is
the finite cohomology computation

    H¹(X,Adj_X * omega_X)_odd.

For a non-Gorenstein compactification one must instead use the actual
canonical module; replacing it by a guessed complete-intersection degree
would give an incorrect test. A finite homogeneous module resolution can
compute the cohomology once this module is known.

The raw three equations in (q,h,t,U,v), after s=U²v, are not automatically
such a global CI model of the desired function field. At v=0 and h=0, or
at v=0 and h²=4, their first two equations vanish identically. The third
equation alone leaves two-dimensional components entirely on v=0. Thus
the correct main-component ideal requires saturation before compactifying.
Any adjoint/canonical computation on the unsaturated CI would mix those
vertical components with the desired surface.

The corrected boundary curve C has a model with conormal degree at least
276, whereas deg(omega_C)=204. Consequently first-neighborhood duality on
this model supplies no obstruction: H⁰(omega_C tensor N_C/S)=0. This
does not determine the global adjoint module. For comparison, blowing up
many points on a plane curve can make its normal bundle arbitrarily
negative while the ambient surface still has irregularity zero.

One may also use

    0 -> omega_S -> omega_S(C) -> omega_C -> 0.

The cokernel of the residue map on H⁰ injects into H¹(omega_S), but equals
it only after controlling H¹(omega_S(C)). Since C is negative here, ample
divisor vanishing cannot simply be invoked. A complete global adjoint
calculation can provide that missing control; boundary residue ranks
alone do not.

Practical next data needed for an exact calculation are a projective or
multigraded ideal of the saturated main component, its dualizing module,
and the conductor/resolution adjoint conditions at all boundary strata.
The P, G, q=0, infinity and J=0 charts now provide verified local data along
the special curve C, but not the remaining global adjoint conditions.
