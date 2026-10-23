# Public quotient-obstruction packet: scope and reproduction audit

Source: discussion 57 reply
`https://github.com/hodge-computer/sextics/discussions/57#discussioncomment-19131907`
and the downloaded gist
`https://gist.github.com/deanodotdotdot/f335056ed117252a6057d57bb9a36d8e`.
The checked local snapshot is gist version
`4d381b220dd3c4d8f6cf83e022960ed6bdf01de9`, updated
`2026-10-22T20:50:33Z`. Its README states stronger results than the earlier
20:21 discussion prose. No external content was changed.

The packet does **not** rule out the full compact rank-four, infinity-extended,
or bare-coordinate current construction. It adds fixed-coordinate necessary
conditions for a final primitive, together with narrowly scoped degree-seven
and degree-eight denominator exclusions.

## Target and snapshot binding

The independent inspection in
`audit/public-quotient-run/inspect_public_packet.py` verifies every one of the
21 entries of the supplied download hash manifest. The baseline compressed
bundle includes a target record whose raw hash is
`5818fa7d710a36ea6f0a3b58f273e8408d50e6c4b3e8aa6f960f432db379dcf6`,
identical to the current target at repository commit
`21fccb6b4f1d4070ddaa30195a78f268247569e6`.

This was not accepted merely on a hash claim: safe AST/Fraction parsing also
checks exact F, A and q equality with both the current record and the original
rendering (`bb0e2891331ddcf18fdbc683df881900400f0e8c2cc73b2f0f23c5d3f7c88467`).
The threefold checker's literal physical polynomial was separately parsed
without executing it and equals the actual X0=1 target. Its monomial
substitution has logarithmic determinant **+36**, and the source exponent
pulls back exactly to `x*y^4*z*a*b` in logarithmic physical coordinates.
Inspection results are saved in `public-quotient-run/inspection-results.json`.

## What is actually newly excluded

The updated README and proof notes say:

* Degree seven: every denominator in one full diagonal character is excluded;
  general mixed-character degree-seven denominators are not excluded.
* Degree eight: 30 of the 36 single-character classes are excluded. The six
  not excluded are `(a,0)`, `a=0,...,5`. This is not a general degree-eight
  exclusion. The count comprises 24 baseline classes and six additional
  classes.
* Separately, degree-eight denominators invariant under the second paired
  diagonal action and odd under X2/Y2 exchange are excluded. This is the
  family `(X2^6-Y2^6)*L` for the stated invariant quadratic L, allowing
  mixtures of the other diagonal characters.
* For the specific torus quotient

      c=x/y^2, d=z/y^3, s=y^6, P=y^3*a*b, U=a^6,

  holding **any one** of these five coordinates fixed admits no relative
  rational primitive in the other four. This permits arbitrary poles and
  finite algebraic extensions. It strengthens the earlier ten tests fixing
  two quotient coordinates, but does not classify nonlinear coordinate
  changes, arbitrary first integrals or all primitives.

The degree-seven/eight unit-ideal packets were read for arithmetic and scope;
their large bounded checkers were not rerun in this audit.

## Threefold proof and arithmetic review

The geometric argument is a second-variation test. A relative exact source
has compact residue in coniveau one of H3. After spreading finitely many
supporting divisors and passing to a finite base cover, their Gysin images
are connection-stable and lie in F1. Hence the F0 part of the second
Gauss-Manin derivative must vanish. The only pole-four contribution is the
stated nonzero scalar multiple of `b_monomial*(theta g)^2`. The toric residue
identification and smooth generic compactification remain mathematical
inputs, with the cited Mavlyutov theorem; they are not proved by executing
the checker or formally verified in Lean here. The localization, Hodge
filtration and finite-trace scope are consistent on review.

The arithmetic rank argument is stronger than modular nonmembership alone.
There are universal Koszul maps `M*K=0`. A mod-101 nonzero minor gives a
generic characteristic-zero lower rank bound for each of M and K, and the
kernel relation gives the opposite upper bound for M. The observed equality

    rank M = 5|L3|-rank K

therefore fixes the exact generic characteristic-zero rank. An augmented
minor then proves nonmembership. Extension from Q(t) to C(t) preserves these
matrix ranks. This logic is sound on inspection.

The contributor's standalone checker was inspected before execution. Its
sparse elimination is exact in F101; its polytope enumeration includes all
lattice multipliers in the stated spaces; its Koszul blocks have disjoint
component supports; and the source and derivative columns have the stated
exponents. It has no external commands or networking. It writes a JSON next
to itself, so an unchanged byte-for-byte copy was placed in the audit-owned
directory before execution. The downloaded snapshot remains unchanged.

The unchanged contributor checker completed successfully, exit code zero.
All five complete JSON reports equal the downloaded reports exactly:

| Passive coordinate | rank K | rank M = upper bound | augmented rank |
| --- | ---: | ---: | ---: |
| c | 1025 | 1200 | 1201 |
| d | 1335 | 1640 | 1641 |
| s | 3025 | 3580 | 3581 |
| P | 1935 | 2510 | 2511 |
| U | 2795 | 3465 | 3466 |

The execution log is `public-quotient-run/contributor-threefold-rerun.log`,
and its hash/status are saved in `contributor-rerun-results.json`. This is a
rerun of contributor code, **not** a new independent rank implementation or an
independent formal proof.

## Consequence for our constructive routes

The word "five" refers to the five ambient quotient coordinates, not five
endpoint basis rows. A compact module of rank four, or its infinity extension,
is a different object. Exact fiber corrections and the physical lift must be
included before testing which quotient components of the actual four-form
primitive vanish.

For a literal physical primitive written by a vector current in ordered
coordinates `(x,y,z,a,b)`, the quotient components, up to common invertible
Jacobian factors, are

    c: Vx/x-2Vy/y,
    d: Vz/z-3Vy/y,
    s: 6Vy/y,
    P: 3Vy/y+Va/a+Vb/b,
    U: 6Va/a.

Thus the result forbids any of these expressions from vanishing identically
in a successful primitive. It does not require that a preliminary compact
current have five independent base columns, and it does not imply that the
full rank-four/infinity/bare PDE is impossible. No such quotient component is
set to zero automatically by those complete construction interfaces.

The existing full-current interfaces should remain active. Any eventual
candidate must be tested after its complete literal transport, using the
original-target identity. No certificate has been found.
