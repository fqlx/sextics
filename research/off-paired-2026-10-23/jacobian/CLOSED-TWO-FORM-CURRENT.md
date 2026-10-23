# An actual closed twoform and its complete remaining source

This is a source-carrying partial current, not a certificate.
`closed-two-form-current.py` checks the formal rational identities below.

Use the complete G36 cubic interface in `../cubic-ray/INTERFACE.md`:

```
f=H+Bp+Cp³,  g=B+3Cp²,  R=Bp/g³,
omega=dz∧dU/(3z²)+dK∧dt/(6t),
Omega=omega²/2=dz∧dU∧dK∧dt/(18tz²).
```

The Poisson bracket has the displayed positive coefficient in the `(z,U)`
and `(K,t)` pairs. For any rational functions `F,G`,
`dF∧dG∧omega={F,G}Omega`.
The subscript `0` below means all base bracket derivatives hold `p` fixed.
Put

```
A={H,B}, D={H,C}, E={B,C},
Q=A+3p²D+2p³E,
N=(3z²f_U,−3z²f_z,6tf_t,−6tf_K).
```

This component convention removes ambiguity between left and right
Hamiltonian-vector conventions. In particular

```
N(p)=0,  N(g)=−Q,  div_Omega(N)=−Q/g,
i_N omega=df_base=−g dp,
i_N Omega=−g dp∧omega.
```

Let

```
S=Bp/Q, F=p²/(2Q),
eta_a=−S dp∧omega/g,
b=F dlog(g)∧omega.
```

The first current satisfies
`d eta_a=[R+N(S)/g²]Omega`. Its old remaining term has a logarithmic
pole at the generic branch after multiplying by the actual `Omega`.
Subtracting the explicit rational threeform `b` gives

```
eta_0=eta_a−b=lambda∧omega,
lambda=−[Bp dp+(p²/2)dg]/(Qg)
      =[p dH+(p²/2)dB−(p⁴/2)dC]/(Qg),
beta_0=d lambda,
d beta_0=0,
beta_0∧omega=d eta_0=(R+R1)Omega,

R1=−p M/(2Q²g),
M=2N(Q)+p{g,Q}_0
 =2{Q,H}_0+p{Q,B}_0−p³{Q,C}_0.
```

All derivatives of `Q` in this formula are retained. In particular `M`
does not mean a coefficient or a universal-parameter derivative. The
identity is global in the actual cubic function field.

## A further closed Q-log correction

The nonlinear geometry agent derived an additional exact closed twoform
which simplifies the remaining source:

```
beta_Q=d[p²/(2Q)]∧dlogQ,
beta_Q∧omega=+[p N(Q)/(Q²g)]Omega.
```

Thus `beta_tilde=beta_0+beta_Q` is closed and satisfies

```
beta_tilde=d lambda_tilde,
lambda_tilde=−p²(dB+3p²dC)/(2Qg),
beta_tilde∧omega=(R+R2)Omega,
R2=−p²{g,Q}_0/(2Q²g).
```

Indeed `lambda+F*dlogQ=lambda_tilde−dF`, with `F=p²/(2Q)`.
This eliminates the entire `N(Q)` contribution, including its derivatives,
without a logarithmic coefficient function. The other `Q` derivative is
still present; no pole at `Q=0` has been cancelled by assumption.
For example at `(z,U,K,t)=(1,1,1,2)`, `{g,Q}_0` modulo the actual cubic is
`103707p²/5+3778244p/75−73476/25`, so this remaining source is nonzero.

## Exact branch-residue primitive

On the generic branch `Dg:g=0` one has `B=−3Cp²,H=2Cp³`. The actual
logarithmic residue of the old correction is

```
Res_Dg [N(S)Omega/g²] = −d_Dg [p² omega_Dg/(2Q)].
```

This is an explicit rational twoform primitive on the branch; no vanishing
of an unspecified proper cohomology class is assumed. One proof uses
`Delta=4B³+27CH²`. On the branch, in the left Hamiltonian convention,

```
X_Delta(p)=18Cp²Q,
X_Delta(Q)=108C²p³N(Q)−108Cp³Q N(C),
Q_p=−6p N(C),
N(S)/Q=−X_Delta(F)/X_Delta(p).
```

Thus `b=F dlog(g)∧omega` cancels exactly this residue, with every
coefficient derivative included.

## What is and is not removed

The **full remaining fourform** `R1 Omega` is regular at the generic
branch `g=0` on the cubic cover where `Q` and the physical coordinate
Jacobian are nonzero. This is stronger than merely cancelling its formal
residue: in the chart `(p,B,C,t)` the pulled-back base volume has an
explicit factor `g`, cancelling the single `g` denominator in `R1`.
The chart exists generically: `det d(H,B,C)/d(z,U,K)` equals `−4` at
`(z,U,K,t)=(1,1,1,2)`.
The independent verifier supplied an actual simple branch point as well:
`z=1,U=−1,K=0,p²=1/12,t=p/3−2`. There `f=g=0`, `g_p=12p!=0`,
the coordinate minor is `−2`, and `Q=−8+5p/6!=0`.

The formula retains a generic double pole at `Q=0`, the physical `z,t`
boundary, and any intersections where these charts fail. It does not
establish a logarithmic extension there or rational exactness. The next
actual construction needed is a closed rational twoform `beta_1` with

```
beta_1∧omega=−R1 Omega.
```

Using the additional Q-log correction replaces this obligation by the
simpler `beta_1∧omega=−R2 Omega`.

There is a precise coefficient-one trap in the next step. If `d_0` means
base differential with `p` held constant, the relative closed twoform

```
gamma=−p² d_0g∧d_0Q/(2Q²g)
     =d_0[−p² d_0log(g)/(2Q)]
```

has relative trace `R2`. Its canonical absolute closed extension is exactly
`beta_tilde=d lambda_tilde`; the implicit `dp` terms add back the original
source `R`. Therefore treating the relative expression as an already
closed absolute twoform would discard the actual source. A different
absolute closed correction or a proved finite operator identity is needed.

Then `beta=beta_0+beta_1` is closed and carries the original source.
With `theta=−dU/(3z)+Kdt/(6t)` and `dtheta=omega`,
`theta∧beta` would be an actual rational threeform primitive of
`R Omega`. No such `beta_1` has been found here.
