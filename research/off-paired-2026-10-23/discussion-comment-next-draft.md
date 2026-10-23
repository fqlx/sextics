> Historical unpublished draft. Superseded by HANDOFF-2026-10-23.md and the live discussion replies; do not publish this draft.

Exact partial results for the immutable `off-paired` target. **No certificate or Lean proof has been found.** The full problem remains open.

[Reproduction packet and detailed arguments](https://gist.github.com/fqlx/2023ba9f5ddc2117c72a03fb9a4c7c55), The mathematical fields $(F,q,A)$ are unchanged between the original record at `d5e9ef223a2cd210517f35c071e9a5108a15e025` and the rendering refresh at `21fccb6b4f1d4070ddaa30195a78f268247569e6`; an independent exact semantic checker verifies both and rejects changed $q$. Standard-library rational/integer scripts have independent SymPy or Singular checks where stated.

**Every legal homogeneous certificate denominator has degree at least seven**, including complex coefficients, nonzero quotient and unrestricted allowed parity. Euler normalization retains the denominator and gives $N(F)=AD$. The full colon dimensions in degrees 0–6 are $0,0,0,0,1,11,54$. The unique quartic direction $D_0=F_{X_0}/(6X_0)$ fails the second equation (complete matrix ranks 67/68). Degree five is excluded by a complete 90-dimensional Koszul kernel and relaxed quadratic ranks 581/647. Degree six is excluded by its complete 315-dimensional kernel, exact square elimination leaving only $\operatorname{span}\{Z_iF_i\}$, and explicit rational Nullstellensatz identities on all five nonzero Euler-gauge charts. `run_degree6.py` replays the full exclusion without Singular; independent audits reconstruct both reductions.

**The explicit surface-only route is now ruled out for this source.** On $X_0=1$, put
$$
u=X_1/Y_0^2,\quad v=X_2^2/Y_0^2,\quad t=Y_0^6,\quad c=Y_1/(X_1Y_0),\quad d=Y_2/(X_2Y_0).
$$
Then
$$
J=c^6u^6t^3+\left(u^6+d^6v^3+\frac{cd}{2}u^4v\right)t^2
+\left(1+v^3+\frac d3uv+\frac c2u^2\right)t+1,
$$
and the exact target density is $ut/12$. Its generic resolved surface has $p_g=2$, $K^2=6$, $q=0$. More strongly, this particular residue class is **outside the generic Picard span**: at the torically regular fiber $c=2,d=3$, all four products $BH_c\eta_j,BH_d\eta_j$ are nonzero in Mavlyutov's single-colon toric residue ring. Independent rational linear algebra supplies a dual functional annihilating all 680 relations but not any target (ranks 442/443). A Picard-span class cannot acquire this $F^0/F^1$ Gauss–Manin derivative. Localization therefore excludes a rational primitive with $c,d$ fixed, even after finite extension. See `relative-primitive-obstruction.txt` and `picard-proof-audit.txt`. This argument must use $c=2,d=3$; $c=d=1$ is quasismooth but not torically regular.

Two further scoped results narrow alternatives. Every saturated monomial surface projection of the full diagonal quotient has positive geometric genus; `toric-projection-obstruction.txt` gives a universal lattice proof using the five maximal hollow width-three polytopes, rather than a bounded projection search. The endpoint genus-two Jacobian is generically absolutely simple: the good specialization $H=C=1$ at 11 has Weil polynomial $T^4+3T^3+10T^2+33T+121$, and Howe–Zhu's criterion excludes geometric splitting. `genus2-simplicity.txt` and `genus2_simple.py` give the exact argument and counts. Thus it has no generic elliptic factor of any degree.

A concrete sufficient construction is now reduced to two polynomial identities in the four base variables. Write $F=X_2^6+Y_2^6+CX_2Y_2+H$, with the exact $H$ and $C$ in `contact-current.txt`. Find nonzero homogeneous $D$ and a base field $M$, $M_0=0$, satisfying
$$
2C M(H)-3H M(C)=2AD,\qquad D\operatorname{div}M-M(D)=0.
$$
Then $E=4D$ and the six explicitly given numerators produce the immutable certificate with $Q=0$; both cleared identities were expanded exactly. **No such $M,D$ has been found.** This is a sufficient construction, not a reformulation of every possible certificate.

A proposed direct genus-two correspondence is also excluded: the genus-19 base-curve Jacobian is ordinary at $H=C=2$ over $\mathbb F_7$ (Hasse–Witt determinant 6), whereas the endpoint genus-two Jacobian has $p$-rank 1. Both reductions are good, so the endpoint cannot be a geometric generic isogeny factor, even after finite extension. See `endpoint-base-ordinary-audit.txt` and its independent standard-library audit.

The current constructive obligation is a full primitive using coefficient directions $c,d$, or a different source-carrying cover or correspondence. These results do **not** exclude the requested physical certificate; denominators of degree seven and higher remain unrestricted.

A constructive continuation reconstructs the full endpoint connection in the compact basis $p^jdp/Z$, $j=0,1,3,4$, and adds the third-kind component $j=2$ with constant opposite residues at infinity. Independent standard-library rational arithmetic checks 75 polynomial identities and the residue calculation, including source orientation and exact target binding. The additional residue current must be divergence-free. No current has been found.

A broader source-carrying interface uses a moving pole: with $\beta_s=dp/((p-s)Z)$ and $s$ held fixed,
$$
(\partial_C-s\partial_H)\beta_s=\partial_H(dp/Z).
$$
The physical choice $s=-3X_0Y_1/2$ cancels the term linear in $Y_0$ in $H+Cs$. A current weighted by the actual physical density still leaves its nonzero density-derivative correction. Explicit elliptic quotients of scalar differentials do not automatically descend this $C$-dependent kernel; all coefficient derivatives and transport corrections remain obligations. These are constructive reductions, not a primitive, Lean proof, or certificate.


A further exact reformulation uses the global-Y-sign quotient. On `X0=1`, put `X1=x,X2=a,Y0=y,Y1=yu,Y2=yv,s=y²`. The actual source becomes `s² dx da ds du dv/(2f²)`, where `f=H+Bs+Cs³`, `H=1+x⁶+a⁶`, `B=xu/2+x³auv/2+xav/3`, and `C=1+u⁶+v⁶`. Its second-pole residue is `Bs/(3Cs²+B)³`. In the trace-free basis `s,s²+2B/(3C)`, rational exactness is equivalent to a full rank-two finite-connection divergence equation over four rational base coordinates; this is not an endpoint-pole truncation. Independent exact Fraction checks verify the connection, the source, completeness over the complex constant field, and conditional transport back to the protected target. An explicit universal coefficient-flow primitive exists, but its physical divergence correction remains unsolved. No certificate follows from the reformulation.

Prepared for `fqlx` with OpenAI Codex assistance, including independent algebra, geometry and verification agents, using the repository's certificate and transport framework and the primary results cited in the packet. This is reproducible mathematical research, not protected Lean verification or acceptance.
