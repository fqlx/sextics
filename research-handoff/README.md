# Hodge Computer research handoff — 2026-10-23

**Stopped at the user's request. No certificate, rational primitive, Lean proof, or accepted solution was obtained.** Six research agents contributed and independently checked selected calculations with OpenAI Codex assistance for `fqlx`. These are research calculations, not protected Lean verification. Do not resume the searches without a new instruction.

The initial choice of `off-paired` as an accessible target was a heuristic, not a proved difficulty ranking. The pinned repository is `hodge-computer/sextics` at `cb551854693127a2542fb405f7ceb47ae0b35a09`. The protected targets, verifier and tracked checkout were unchanged. Later work also covered `cyclic-triple-residual`, `eight-plane-configuration`, `four-plus-two-residual` and a preliminary Klein construction.

## Read first

The paths below are relative to the packaged `research/` directory. Lower-level notes and logs preserve historical experiments, including unsuccessful and superseded approaches. This handoff and the final route READMEs take precedence over old active-search wording. In particular:

- The Chebyshev apparent one-dimensional interpolation shortage is **withdrawn**: its trace-dual filtration was wrong. `global_adjoint_with_RES.*` is an invalid geometric obstruction, retained only as an arithmetic record.
- Local geometric genus on an exceptional surface does not establish global serving cohomology or the actual source's Gysin image.
- Generic cyclic scalar currents are excluded only for the stated scalar route. Bounded current screens do not exclude unrestricted certificates.
- The special-P0 adjoint-sufficiency argument and the inference from the T0 exceptional surface to rationality/klt of the full threefold have **not** received independent geometric verification.
- The generic elliptic infinity chart does not regularize the full physical D32 family. The later Newton valuation is essential.

## Cyclic-triple-residual: reusable exact differential machinery

Target: `q=1`, `A=X0^3*Y0^3`; `instance.rec` SHA-256 `c5713bc06b37db0a64123364f8687a8ebc82e9722cc39ba88357659768eed0bc`.

The clean rank-three proper eigensystem and its conjugate are implemented for

```
C = W^6 + (5/7)(h^3+h*t)W^3 + L*h^6 + r*h^4*t + t^3/x.
```

The complete Q8/Q14 exact corrections remove the apparent frame poles. The actual singular factors are `x`, `D1=27*L^2+4*r^3*x`, and the elliptic discriminant `D2`. The full free logarithmic module, polynomial connection contractions, physical source pullback and orientation were audited. Start with [the clean frame](research/round9/cyclic_full/CLEAN-FRAME.md).

Adding graph-pole forms `sigma0=Res(h^4*Omega/((t-s*h^2)*C))` and `sigma1=Res(W^3*h*Omega/((t-s*h^2)*C))` gives a complete rank-five connection. All eight boundary reduction rows retain their exact primitives; all six curvature pairs vanish over the rational function field. Independent ordinary-form, residue-block, polarization and physical-jet audits passed. The source-specific graph is `s=Teff=N1/N0`; its derivatives and the cube-root density character are retained. See [rank-five setup](research/round10/horizontal5/README.md), [boundary reductions](research/round9/open_curve/README.md), and [independent audit index](research/round11/klein_coupled_handoff/VERIFIED_CYCLIC_PACKET_INDEX.md).

This is differential machinery, not a source-serving current. The displayed finite proper, marked-log, radial and closed-seed modules were inconsistent in their stated bounds. No unrestricted current obstruction follows.

### A complete fixed-support exclusion

The literal reduced support

```
D = X2^6 + Y0^6 + Y1^6 + Y2^6
```

cannot serve this source, including arbitrary complex coefficients and nonzero quotient. The complete normalized system has 2,760 rows and 1,248 columns (1,129 numerator, 119 quotient). Modulo 1,000,003 its coefficient/augmented ranks are 1,236/1,237. Twelve exact independent homogeneous kernels give the matching characteristic-zero rank upper bound. The rank sandwich proves the exclusion over C. The repository's prescribed-support theorem extends this to all pole multiplicities with the same reduced support; adjoining new components is outside the claim.

Root and another agent independently rebuilt the system and replayed the kernels. See [proof and code](research/round10/fermat_cone_fixed/README.md), `search.py`, `result.json`, `packet.pickle`, and the separate `round10/portfolio/audit_fermat_fixed.py/json`. The second tested Fermat support has only a modular negative; it is not included in this exact exclusion.

### Actual D32 geometry and remaining gap

The effective graph has degree 32 and 558 terms. Verified pieces include:

- A finite conductor repair with generator `theta=q*S/Y1`, `S=Y0^6+Y2^6`, and quotient `O_union(-25)`. This repair adds neither global H1 nor H2. It is not complete global normalization. See [conductor work](research/round10/conductor_collision/README.md), especially `global_normalization.py`.
- The actual generic Fermat/conductor corner is a quasismooth weighted CI of degrees `(12,12)` in weights `(3,2,6,6)`, transverse geometric genus 10. The relevant Y-even adjoint slots are `1, epsilon^2, b, r`. Explicit generic jet preimages do not yet satisfy every global correction.
- Along the 36 actual infinity conductor lines away endpoints, the normalized double cover has Newton vertices `(0,6),(2,3),(6,1),(14,0)`, adjoint ideal `(u^2,b,r)`, and transverse geometric genus 2. The homogeneous condition is `P in (S,Y1^2,Y1*X0^2)`. See [actual boundary audits](research/round10/horizontal5/fresh/boundary/README.md).
- The later actual vertex has weights `(X0,X1,X2,Y1)=(7,5,5,16)`, F-order 30 and D-order 155. The main coarse residual component is rational, but the necessary canonical extension filter is still `wt(P|X)>=123`. See [vertex handoff](research/round11/d32_corner_elliptic/README.md). The earlier coarse elliptic surface has geometric genus 12 but the wrong source character; conormal layers cannot be omitted.
- The normalized generic Gamma initial-cone calculation gives graded dimensions `60,49,39,30,22,15,10,6,3,1` and explicit proposed dual degree-32 jet lifts. Their compatibility with the actual resolution/global Leray map and special points is unresolved.

**Next mathematical obligation:** complete actual normalization, endpoint/special-point and thickening corrections, then compute the complete global adjoint/Leray map and the Gysin image of the pinned source. Neither nonzero global serving H20 nor a primitive has been proved.

The earlier generic one-direction scalar equation is separately excluded over `C(eta,V,s)`, also after finite algebraic extension by trace; see `round8/off_paired_B_resonance/resonance_obstruction.md` and its independent contracted audit. This does not exclude other coupled or moved-ratio constructions.

## Off-paired: Chebyshev cover and corrected interpolation

[The complete Chebyshev handoff](research/round9/chebyshev/README.md) gives both degree-three quotient maps and the actual source-sensitive elliptic differential. The second quotient satisfies `dx/y=s*k*dk/Z`; dropping that factor would change the source.

An exact global degree-six finite-flat normal algebra and the full inverse minimal-line module are implemented. The latter pushforward has summand degrees

```
(-14,-3), (-6,-4), (-10,-7), (-14,-8), (-10,-5), (-18,-5).
```

Hence the normal-base mixed coherent cohomology vanishes. The nontrivial `q=infinity,h=0` corner is a degree-two base change of a rational elliptic surface, with local geometric genus 2; independent replay is in `round10/chebyshev_corner/elliptic_basechange.py/json`.

The actual trace-duals invalidate the earlier 20/19 interpolation block and its proposed source coincidence. The corrected 73 proposed upper boundary jets have full-rank interpolation. **Gap:** prove that the normalized resolution/corner inventory and adjoint spaces are complete. No global exclusion or certificate follows yet.

Prior discussion results remain credited to `fqlx`, `benediamond` and `deanodotdotdot`; this pass does not supersede their independently scoped obstructions. See [discussion 57](https://github.com/hodge-computer/sextics/discussions/57) and its linked original packets.

## Other targets

- **Eight-plane:** exact source reductions through quartic Hermite/Ferrari transfer and a simpler global-Y cubic are in [quartic notes](research/round8/eight_plane_quartic/README.md) and [independent audits](research/round8/eight_plane_audit/README.md). Every one of the six complementary coordinate 3+3 Euler supports containing X0 and excluding Y0 fails the complete E2 test over C: ranks 742/743 with 35 exact independent kernels. This is a finite support list. Selected moving-Segre cubics supply only 35 globally exact source directions; bounded rational currents did not produce a primitive.
- **Four-plus-two:** [the portfolio packet](research/round10/portfolio/README.md) constructs a genus-seven signed-radical incidence retaining the actual three-dimensional anti-Prym sector. Its correspondence composition is `4*id` on that sector; a simpler genus-three quotient loses the character. `trigonal_resolvent.py/json` verifies the resultant and incidence projector over QQ. A serving support/contraction remains missing; the generic fixed-ratio surface still has two anti holomorphic two-forms.
- **Klein:** [preliminary handoff](research/round11/klein_coupled_handoff/HANDOFF.md) and `identities.py/json` preserve the source's character in a genus-three line curve. The global cyclic twist is essential, the universal cover alone supplies no useful nontrivial H1 character, and the actual additional finite cover and source Gysin remain uncomputed. The k1 Borel-Weil-Bott contribution must not be omitted.
- **Cycle-q2:** no new primitive was obtained. Downloaded prior authors' bulk packets are omitted rather than republished as work from this pass.

## Reproduce and provenance

This research snapshot is on a dedicated branch in `fqlx/sextics`, not a solve submission. Its parent is the pinned repository commit. `manifest.json` records every supplied research file's SHA-256, byte size, and the exact target-record hashes. Tool binaries, caches, large obsolete scalar HNF transcripts, HTML snapshots, and third-party bulk downloads are omitted.

Place this checkout at `/workspace/sextics`, and expose its `research-handoff/research/` directory as `/workspace/research` (a symlink is sufficient in a fresh workspace). Many scripts use these absolute paths. Python 3.12.14 was used with SymPy 1.14.0, python-flint 0.9.0, PyYAML 6.0.3, NumPy 2.3.5 and SciPy 1.17.0. Some geometry audits need Singular; replace the historical `/workspace/research/tools/algebra/bin/Singular` path with the installed executable, or link it there. No algebra-system binaries are bundled. Optional old Wiedemann code can rebuild its helper with `cc -O3 -shared -fPIC -o wiedemann_bm.so wiedemann_bm.c` in `round5/current`.

Representative replays (each writes results beside its script; this is not a command to launch every archived search):

```sh
python /workspace/research/round10/fermat_cone_fixed/search.py
python /workspace/research/round10/portfolio/audit_fermat_fixed.py
python /workspace/research/round9/abel_prym/rank5_flatness_audit.py
python /workspace/research/round10/conductor_collision/global_normalization.py
python /workspace/research/round10/horizontal5/fresh/boundary/infinity_line_audit.py
python /workspace/research/round11/d32_corner_elliptic/vertex_newton.py
python /workspace/research/round9/chebyshev/trace_duals.py
python /workspace/research/round9/chebyshev/global_adjoint_interpolation.py
python /workspace/research/round10/portfolio/trigonal_resolvent.py
python /workspace/research/round11/klein_coupled_handoff/identities.py
```

Archived receipts distinguish exact QQ identities, finite-prime rank sandwiches, modular-only screens and geometric arguments. Not every archived script was rerun while assembling this handoff. Final agent notes identify checks actually performed and unaudited implications.

Earlier conjugate-reference/scalar inputs are retained with credit to the [previous `fqlx` cyclic packet](https://gist.github.com/fqlx/3e90a700d3631f9218680c27857f7741/b28663e84c720043e7200f8aa0a9e8ee58b6782b). The repository's certificate/transport framework and the human mathematical references in the route notes remain prerequisites. No solve, acceptance, or human review of all AI-generated mathematics is implied.
