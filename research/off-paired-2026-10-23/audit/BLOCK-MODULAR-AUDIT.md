# Independent audit of blocked modular elimination

The audited solver is `endpoint/additive/block_modular.py`, SHA-256
`d9c7ed9a7c8cff1b5d5bec7386d48f53c7a824b8be0f1254ea5bf1620b8d190b`.
No numerical or pivot-logic discrepancy was found within the enforced bounds.

## Exactness bounds

Inputs must be canonical integers in \([0,p)\). For panel width \(k\), the
enforced condition
\[
k(p-1)^2<2^{53}
\]
makes every nonnegative integer BLAS product and every partial sum exactly
representable in binary64. Delayed subtraction is also an exactly representable
integer with absolute value below this bound. Scalar row normalization and
panel outer products are bounded by \((p-1)^2\). Taking the modular remainder
returns canonical integer values before the next update. The implementation's
ordinary NumPy/BLAS arithmetic was stressed near this bound in the independent
comparisons below.

The float bound alone does not control the later int64 dot products. The solver
now separately enforces
\[
n(p-1)^2<2^{63}
\]
for the back substitution and final `mat @ sol` verification. Without this
second bound, the general exactness claim would be incomplete. Canonical
integer-input assertions were also added before this audited version.

For the actual \(p=1009,n=2740,k=48\) run, the two bounds are only
48,771,072 and 2,784,015,360, respectively.

## Pivot and deferred-update invariant

The active panel columns are updated immediately. The corresponding trailing
updates are delayed, with their elimination multipliers stored in `L`. Before
normalizing a newly selected pivot row, its accumulated trailing update is
applied against the already normalized pivot rows. Row swaps apply to both
the augmented matrix and `L`, preserving that invariant. At panel end the same
update is applied once to all remaining active rows. The right-hand side is in
the trailing block, so consistency receives the same operations. Previous
pivots are never swapped into active rows. Skipped columns are zero in all
active rows. Back substitution sets free variables to zero and uses the final
row-echelon equations. Zero coefficient rows with nonzero right-hand side are
therefore exactly the inconsistency condition.

## Independent checks

`audit_block_modular.py` generated systems with known rank and consistency
through invertible row and column operations. It compared the solver against
the older integer modular elimination and checked every returned solution using
Python-integer dot products. This avoids relying on the solver's own int64
verification. It passed 396 comparisons on 99 systems with:

- Empty, zero, dependent, tall, wide, consistent and inconsistent systems.
- Long skipped leading-column panels and row permutations.
- Primes 2, 101, 1009, 1,000,003 and 13,500,007.
- Panel widths 1, 7, 17 and 48.
- Designed bulk and pivot-row delayed sums near the binary64 limit.

The largest designed dot was
8,748,007,776,001,728, below \(2^{53}=9,007,199,254,740,992\).
The adjacent JSON records every comparison and the exact audited solver hash.

## Meaning of the research run

The merged \(H,+,-\) script assembles the covariant derivative of each
\(P/D\) summand with its full denominator derivative, then tests their sum
against the physical source. Its first run used 2,740 columns, 1,434 generic
points and 7,170 scalar rows; the recorded rank is 2,675 and the sampled
system is inconsistent modulo 1009. Stopping at that inconsistent subset is
valid finite-field search feedback. It is not a proof of unrestricted
nonexistence or, without additional good-reduction arguments, an exact
characteristic-zero exclusion.

The script correctly refuses to promote partial consistency to a candidate.
It increases to at least one generic point per unknown, then requires fresh
points. Even surviving those stages gives only a modular candidate. Exact
rational reconstruction, the literal current and transport identities, and the
complete physical polynomial certificate still have to be verified.
