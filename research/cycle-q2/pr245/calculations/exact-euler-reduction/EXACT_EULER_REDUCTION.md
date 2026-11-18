# Exact genus-ten Euler primitive and the single remaining tensor

Use the physical complete genus-ten curve at fixed I,J:
v=I/b, U=Tv³, W=T+1/T+v/2,
J=W+f(U), f(U)=I³/U+U³/I³, and h=6−6T²+vT. The Newton form
φ=φ₆₂=b⁵ T db/P_T equals 2T dU/(I³ h) as rational one-forms since
bP_b+3TP_T=−b⁹h/2 on the quartic. Let ψ=∇_Jφ.

At fixed U write X=∂T|_U and B=−6T²X/h; W_T|_U=−h/(6T²), so B
is the lift of ∂J holding I and U constant. Put P=2B(T/h). Then
I³ψ is represented by P dU. The lift of ∂I fixing U equals
∂I|_(T,U)−f_I B. Differentiating I⁻³ therefore gives

    (I³/3)(7+2I∇_I+3J∇_J)ψ
      = [P/3+(J−2I f_I/3)B(P)]dU

as a relative form using these fixed-U lifts. On the fixed-moduli curve
J−2I f_I/3=W+Uf'(U), f'(U)dU=−dW. Since
W_U|_T=v/(6U), this relative form is

    G=[P/3+(T+1/T+v/3)B(P)]dU − U X(P)dT.

In the two independent plane coordinates T,h, set v=(h−6+6T²)/T
and U=Tv³.
The physical second-kind form from the earlier packet is

    η=[C+64] dT/T +9952T dT +(1728T²−48) dh/h +288 dh,
    C=Σ_{k=1..5} a_(−k−1)(T²)/(3k h^k)−16h/3.

The exact positive identity is η−G=dR(T,h) on the whole rational
(T,h) plane. The following table gives R. Row k lists the coefficients
of T^(2k) h^e in increasing columns e=−4,−3,−2,−1,0,1.

       k     −4       −3       −2      −1      0      1
       0   −93312    76032   −20736    2160       0    276
       1    93312    62208   −28512   −7776    5352      0
       2   839808  −269568  −114048   47088       0      0
       3  −466560  −698112   256608       0       0      0
       4 −1492992   829440        0       0       0      0
       5  1119744        0        0       0       0      0

The sibling euler_primitive.py reconstructs both coefficients of G
and η in Q[T^±1,h^±1]. It verifies equality of their exterior
derivatives, integrates the difference, and verifies both coefficients
after differentiating the displayed twenty-term rational primitive.
There is no specialization, denominator-degree cutoff, or remaining
equation in this verification. Restriction to the physical curve proves

    (7+2I∇_I+3J∇_J)ψ = 3[η]/I³.

## Source transfer

The surviving proper physical source was e_τ⊗w where w=−[η]/(4I).
Let ω=dτ/F_y and e_τ=τω on the genus-four curve. Its established
transport identity is
∇_I(ω+2I e_τ)+∇_J(3J e_τ)=3e_τ modulo a literal relative derivative.
Thus (2+2I∇_I+3J∇_J)e_τ=−∇_Iω. In the quotient of the tensor
product by the two full covariant derivative images, integration by
parts with the new Euler identity yields

    e_τ⊗w ≡ (I²/12)(2+2I∇_I+3J∇_J)e_τ ⊗ ψ
            = −(I²/12)(∇_Iω)⊗ψ.

A further literal genus-ten relative transport takes ξ=Tdb/b⁴. It
has only two possible toric poles, both of order four with zero
residue; all other points are regular. On the toric branches where
a fourth-order pole can occur, the next correction in the local
unit T/b^(9/4) at b=0 has order at least five, and in T/b^(9/2) at
the corresponding infinity point has order at least nine. This
verifies the zero-residue assertion in characteristic zero.
At fixed b one has

    ∇_J ξ=φ₆₂ (literal),
    ∇_I ξ=−(2/I)ξ−φ₅₂/6−(2/I)φ₉₁−(2/(3I))d_D(T/b³).

The second identity follows from P=0 and
P_T D_b(T/b³)=3b⁵−3b⁵T²+(I/2)b⁴T. In particular for the holomorphic
D section H=(I²/6)φ₅₂+2Iφ₉₁ we have ∇_I(I²ξ)=−H in the proper class.

Since ψ=∇_J²ξ, transfer both J derivatives and the one I derivative,
using flatness. Explicitly,

    −(I²/12)(∇_Iω)⊗∇_J²ξ
       ≡ (1/12)ω⊗∇_J²∇_I(I²ξ)
       ≡ −(1/12)(∇_J²ω)⊗H.

This gives the precise remaining product: the second J derivative of
the genus-four holomorphic ω tensored with one explicit holomorphic
section of D. The reduction supplies actual rational corrections;
no primitive for this last product has been established here.
