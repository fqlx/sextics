# A full two-direction transport in the genus-ten holomorphic frame

Let φᵢⱼ=b^(i−1)T^(j−1) db/P_T on the physical genus-ten quartic and put

    K=−12φ₇₁−8φ₁₀,₁−(11I/3)φ₆₂+6Jφ₇₂,     ℓ=T/b².

Then there is the literal relative one-form identity

    K=(10/3)T db/b³ − (4/3)d_D ℓ.

Indeed, writing U=I³T/b³ and h=6−6T²+IT/b, the equation
P=I⁶T⁴+b⁹T²+(Ib⁸/2−Jb⁹)T+b¹²+b⁹=0 gives

    bP_b+3TP_T−12P=−b⁹h/2,
    d_D U=I³ b⁵h db/(2P_T).

Substitution into 2T db/b³−4b d_DU/(3I³) yields both expressions
for K. Thus the proper class of K has an elementary representative
with coefficient T/b³.

At fixed b, ∇_J(T db/b³) is exactly φ₇₂. The I derivative is
−(6I⁵T⁴/b³+b⁵T/2) db/P_T. To reduce its numerator use

    P_T D_bℓ ≡ −5b⁶T²−I b⁵T+3J b⁶T−4b⁹−b⁶  (mod P).

After eliminating T⁴ with P=0 and then eliminating b⁶T², this yields
the following two proper-class identities:

    ∇_J K=(10/3)φ₇₂,
    ∇_I K=(16/I)φ₇₁+(4/I)φ₁₀,₁+(13/3)φ₆₂−(8J/I)φ₇₂.

The literal correction for the first equation is −(4/3)d_D(D_Jℓ).
For the second it is −4d_Dℓ/I−(4/3)d_D(D_Iℓ).
Here D_s=∂s−P_s/P_T ∂T are the same fixed-b lifts used in the
connection check. In particular K is a common kernel vector of both
maps from holomorphic sections via the Gauss–Manin connection into
H¹(𝒪_D). The symmetry of the two Kodaira–Spencer pairings, combined
with the checked nine-column minor, shows their joint lower image is
exactly the nine-dimensional annihilator of K. The physical [η] pairs
nontrivially with K. Hence the two inputs of the original mixed curl
cannot both have only holomorphic genus-ten coefficients, even with
arbitrary rational functions of the moduli and a full genus-four factor.

## An explicit realization of this one-dimensional quotient

For w=I/2+J and the independent form σ of GENUS_TEN_BASIS.md, let
S=wσ/4. The double pole at P₀ gives ⟨σ,K⟩=4/w, so ⟨S,K⟩=1.
Pairing the written connection equations for K with S gives

    ⟨∇_J S,K⟩=0,    ⟨∇_I S,K⟩=3/I.

Consequently currents A⊗S,B⊗S in the actual genus-four tensor map
under the projection onto this quotient to

    (∇_I^C+3/I)A−∇_J^C B.

The quotient forcing is ⟨w_D,K⟩ e_τ, where w_D=−[η]/(4I), and
the scalar factor is the indicated explicit linear combination of
known Serre pairings. Multiplication by I³ conjugates the shifted
operator to the ordinary genus-four covariant curl. This isolates an
actual necessary scalar component and gives a constructive current
template for it. It does not yet solve the remaining tensor equation.
