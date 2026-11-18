# One cyclic differential and three scalar unknowns on the actual plane-sextic fibration

Work over the base field k=ℂ(τ,b,T) of ONE_FORM_CURRENT.md. The functions A,B,C
are algebraically independent; k is finite separable over ℂ(A,B,C).
Write S_A,S_B,S_C for the unique extensions of the three parameter derivatives
to k. In particular S_C=S=V/E from the current note. These commute. Since
dA∧dB∧dC=−3ABE ν, the new protected residual for the proper-curve
curl problem is hω₀/(36ABE) in the volume dA∧dB∧dC.

## Affine forms and the connection

Let F=A Y⁶+B X⁶+XY+X+Y+C. On F=0 write
m_ij=X^iY^j for 0≤i,j≤4 and ω_ij=m_ij dX/F_Y. These are residues
of m_ij dX∧dY/F, with one fixed orientation throughout.
The 25 affine classes are linearly independent generically. The following
elementary test takes account of all rational exact relations. The six
points at infinity are distinct, and X,Y have pole order one there.
dX/F_Y has a zero of order three at each. A combination of the ω_ij
has poles of order at most five and no finite poles. If it is dR,
then R has no finite pole and has poles of order at most four at infinity.
Sections of O(4) on the smooth plane sextic are restrictions of ordinary
polynomials of total degree ≤4, by the plane hypersurface exact sequence.
Writing R as such a polynomial, its differential is
(F_Y R_X−F_X R_Y)dX/F_Y. Polynomial equality on the affine curve may
also use multiples of F with quotient of degree ≤2. Thus independence
follows from independence in all 45 monomials of degrees ≤8 of

* the 25 m_ij;
* the Jacobian derivative F_Y R_X−F_X R_Y for each of 14 nonconstant monomials R of degree ≤4;
* the six mF for monomials m of degree ≤2.

In the stated column ordering this determinant equals 3 modulo 101 at
(A,B,C)=(2,3,5). All formulas are rational of good reduction there.
The complete generic curve has genus 10 and the punctured curve, with
six points at infinity, has affine de Rham dimension 20+6−1=25.
Thus the ω_ij are a basis of the affine cohomology. The ordinary proper
cohomology injects there, and ω₀₀ is holomorphic.

The partials F_X=6B X⁵+Y+1, F_Y=6A Y⁵+X+1 are a Gröbner basis for
graded lexicographic order by coprime leading terms. Divide F m_i by
them to get

    F m_i = Σ_j M_ji m_j + u_i F_X + v_i F_Y.

Here division can use either partial first whenever both are available;
the implementation fixes X first. The polynomial div_i=∂X u_i+∂Y v_i
in this division already lies in the span of the m_j; set D_ji to its
coefficient. Equating rational meromorphic residues modulo total
derivatives from div_i gives

    G=(D−Id) M⁻¹,       ∇_C ω_i=Σ_j G_ji ω_j.

Indeed u_i F_X/F² and v_i F_Y/F² are congruent to
(∂X u_i+∂Y v_i)/F by ordinary differentiation. M=M₀+C Id and D
are independent of C except for the indicated diagonal of M.
The determinant of M is 28 at the first test point in F101;
invertibility also checks there is no affine singularity. Infinity
is smooth because both leading coefficients are nonzero.

For the single starting section ω₀=ω₀₀ the two other connection
columns are obtained without further linear reduction:

    6A ∇_Aω₀=−ω₀−∇_C(ω₁₁+ω₀₁),
    6B ∇_Bω₀=−ω₀−∇_C(ω₁₁+ω₁₀).

These follow from multiplying F_Y by Y or F_X by X and doing the same
single integration by parts.

## Cyclicity and the exact scalar equation

Put e_i=(∇_C)^iω₀. Compute their coordinate columns recursively by
differentiating each coefficient and then adding the connection G
times the preceding column. In character zero one can compute every
function of A,B,C by this same recurrence. At a field point every
C-Taylor coefficient of G is (-1)^k(D−Id) M^(-k-1).
This accounts for all varying coefficients in the high derivatives.
The generic 20-column cyclic matrix has rank 20, as its selected
minor is 52 modulo 101 at (2,3,5). An independent second specialization
at (3,5,2) modulo 103 gives minor 28. All twenty sections lie in the
proper connection. They form a basis of this dimension-20 subspace.
Let L_j, a_j, b_j be the unique rational coordinates

    e₂₀=Σ_{0≤j<20} L_j e_j,
    ∇_A ω₀=Σ a_j e_j,     ∇_B ω₀=Σ b_j e_j.

These lie in ℚ(A,B,C), and are explicitly computed by the three
matrix divisions from the displayed formulas. Consider three scalar
operators on k:

    L* u = (−S_C)^20 u − Σ (−S_C)^j(L_j u),
    P* v = S_A v + Σ (−S_C)^j(a_j v),
    Q* w = S_B w + Σ (−S_C)^j(b_j w).

The complete proper-curve covariant-divergence problem on the actual
three-variable base is equivalent to one scalar equation in three
unrestricted rational functions

    h/(36ABE)=L* u + P* v + Q* w.

In fact, modulo the additive image of ∇_C, the Leibniz rule gives
e_j f ≡ ω₀ (−S_C)^j f. Thus the first quotient is k/L*(k) as a
vector space over the common constants; the inverse is f ↦ ω₀ f.
Reducing the ∇_C image on the cyclic basis verifies both directions,
including the sole additional relation coming from e₂₀. Flatness
allows ∇_A and ∇_B to act on that quotient. On ω₀v and ω₀w they
give the stated P* and Q*. This proves the equivalence.

A rational solution supplies rational proper connection currents, hence a
rational three-form primitive on the full fourfold. Representatives of
these currents are relative one-forms; wedge with the corresponding two
base differentials, then correct a remaining fibrewise exact one-form
by wedging its rational function primitive with all three base
differentials. The scalar equation is an exact criterion for this proper
subproblem; more general fourfold primitives may use additional supports.

## Reproduction

Run cyclic25.py in Python with NumPy, or invoke
cyclic25.py --prime 103 --value 3 5 2 for the second check. Both scripts'
outputs include every pivot row and all 60 specialized coefficients;
a nonzero modular determinant proves the corresponding rational function
is nonzero in characteristic zero. No claim of scalar solvability is made.
Prepared with OpenAI ChatGPT assistance.
