# A second independent proper section of the genus-ten cohomology

Put χ=T² db/(2b⁶). In the chart of EXACT_EULER_REDUCTION.md it has the following literal derivatives at fixed b:

```text
 ∇_Jχ=φ_{4,3},   
 I∇_Iχ=-10χ/3-(I/6)φ_{3,3}-2φ_{7,2}-(1/3)d_D(T²/b⁵).
```

These follow by multiplying both rational expressions by the relevant monomial times P_T, then using

```text
 -IP_I-(2/3)bP_b+(I/6)b⁸T+2b^{12}=-6P.
```

More generally one applies the same certificate to χ_{ij}=b^(i−10)T^(j−1)db/(j−1); the final derivative for this family is −2d_D(b^(i−9)T^(j−1))/(3(j−1)). After adjoining a cube root of I, both derivatives of I^(10/3)χ are holomorphic in the proper module. Alternatively one may keep the connection twist over the physical field.

Its only possible poles are the following two toric points. At b=s⁴ and T=c₀s⁹(1+O(s⁵)), c₀⁴=−I⁻⁶, χ=2c₀²s⁻³(1+O(s⁵))ds. At b=s⁻² and T=c₁s⁻⁹(1+O(s⁹)), c₁²=−I⁻⁶, χ=−c₁²s⁻⁹(1+O(s⁹))ds. Hence no residues occur. The vanishing orders of φ_{ij} at these points are 4i+9j−37 and 35−2i−9j. Since all ten Newton points have distinct orders at each of these two places, the only holomorphic differential with nonzero pairing against χ is φ₅₂. In the convention ΣRes((∫χ)φ) the residues are −1/I⁶ and −1/(8I⁶), respectively. Thus the total is −9/(8I⁶), whereas the previously used ξ=T db/b⁴ pairs only with φ₃₃. The sections are independent modulo the holomorphic subspace.

This supplies additional explicit mixed currents using any compensating closed pair on the genus-four side. It establishes no primitive for the final tensor by itself.
