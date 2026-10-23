# Exact ell-direction source and its compact transfer

This retains the source-bound K and the full physical cover. It does not
assert exactness of the remaining compact form. The parent reduction and
its thirteen exact transport checks are in
`../../audit/quadric-kernel/QUADRIC-KERNEL-REDUCTION.md`.

Use the fixed quadric and norm pencil

```
Q=a²+b²+i ell²+j a ell+ell+1=0,
ab=h ell³,
h²=f(w)=1/v(i,j²,w),
V=i ell²+ell+1,
P=a⁴+j ell a³+V a²+f ell⁶=0,
Jcurve=a(2a+j ell)−2b²=P_a/a.
```

The positive scalar-lift remainder is the exact four-form

```
S=(K f_w/6) beta wedge dw wedge di wedge dj,
beta=ell²(a²+j ell a+V)dell/P_a.
```

K includes every derivative of the actual w cover. The original immutable
source uses the overall sign specified by the parent scalar reduction.

## A literal relative connection identity

Put zeta0=b dell/ell. At fixed i,j,h, the ell curve has the following
literal parameter derivatives, in a chart with ell held fixed:

```
zeta_i=b ell dell/Jcurve,
zeta_j=h ell³ dell/Jcurve,
zeta_h=ell²(2a+j ell)dell/Jcurve.
```

They follow by differentiating both Q and ab=h ell³. They include the norm
variation; varying h while holding a or b fixed would give a wrong form.
The source differential has the particularly simple exact decomposition

```
beta=zeta0/(2h)−zeta_h/2.
```

At Pa±, ell=0,a=0,b=±sqrt(−1), beta has residues
`±sqrt(−1)/(2h)`. It has no Pb poles. Thus the source Pa residue is

```
±sqrt(−1) (K/6) dh wedge di wedge dj.
```

These residues prevent a rational ell primitive for the uncorrected source
alone. They are actual source coefficients to serve using base currents,
not a bounded denominator failure. The accumulated actual source Green
currents supply their rational scalar primitive; no new assertion that an
arbitrary rational three-form integrates is needed.

## Source bound scalar primitive and the resulting compact form

Choose base volume mu=di wedge dj wedge dw. Let the full scalar primitive,
as extracted from the actual source currents, be

```
B=B_i dj wedge dw+B_j dw wedge di+B_w di wedge dj,
dB=(K h_w/6) mu.
```

The finite-residue agent derives this B by taking residues in the already
constructed source integrations, Green currents, Z transfer, and quadric
current. Consequently its i,j,w dependence is source bound. In particular
B is not to be replaced by a w-only antiderivative.

Since `d(zeta0 wedge B)=d zeta0 wedge B−zeta0 wedge dB`, the explicit
current `−zeta0 wedge B` leaves the following relative compact form times mu:

```
Ccompact=−B_i zeta_i−B_j zeta_j
 −[B_i h_i+B_j h_j+B_w h_w+K h h_w/6] zeta_h.          (Compact)
```

All physical chain terms h_i,h_j,h_w remain. Equivalently, the first three
terms use the total physical derivatives of zeta0, not fixed-h partials.
The three displayed parameter derivatives have no finite residues; the
infinity residues of zeta0 are identically zero, so their infinity residues
also vanish. Higher second-kind poles are retained. Thus (Compact) is a
concrete rank-eight compact source carried by three first connection
directions. Its coefficients depend on the full actual K/current history.

The reduction does not prove that this compact source vanishes or has a
rational primitive. Its complete connection, the explicit source B, and
all eight components must still be used. `verify_quartic_ell_source.py`
passes eleven exact curve, finite-pole, density, and compact-transfer
identities, including all i,j chain terms.
