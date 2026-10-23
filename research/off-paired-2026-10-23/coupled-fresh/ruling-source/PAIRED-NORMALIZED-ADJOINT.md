# Source-carrying paired adjoint in three normalized moduli

Status: exact reduction of this constructive mechanism; no certificate.
The density H is the actual source density from
`NORMALIZED-MODULI-DENSITY.md`, with its finite algebraic cover retained.

Normalize `A=B=T=1`, write `u=c−d²/4`, and use coordinates `(u,d,e)`.
Their volume equals `dc dd de`. Put

```
S=partial_d at fixed u,e,
V=−(u/3)partial_u−(d/6)partial_d−(2e/3)partial_e,
U=partial_e+[e/(2u)]V,
lambda²=−1/u, rho²=e²/(4u)−1,
kappa=rho/(lambda u), n=2rho/(lambda d)=(2u/d)kappa.
```

The physical lifts of these directions are respectively
`(D/d)VS`, `T VT`, and `(E/e)VE` for the last coordinate derivative
`partial_e`; U follows from their displayed linear combination.
Thus all derivatives of these normalizing factors must be retained.

Use the unnormalized beta together with its full infinity term. The
literal shear identity gives

```
q eta_b=−kappa S beta+fiber-exact,
eta_b=n U beta−n M omega_inf+fiber-exact,
M=3lambda/(2rho c0), c0²=−1.
```

The second identity follows from the centered E translation, including
its moving infinity residue. The equality of the two source expressions
becomes

```
partial_e eta_b=(V+1/6)(q eta_b)+fiber-exact.
```

Here `1/6` is the T-scaling character of q eta_b; it is essential.
Consequently the source-free second-order relation is

```
P beta−partial_e(n M omega_inf)=fiber-exact,
P=partial_e o nU+(V+1/6) o kappa S.                    (1)
```

Replacing beta by beta_hat requires expanding every derivative of
`c_inf omega_inf`. Equation (1) is an economical way to retain them.

## Simultaneous finite and infinity closure

The actual source is `−H partial_e eta_b dc dd de`. The T/S construction
has finite ruling residual

```
g beta dc dd de,
g=kappa S[(V−4/3)H].                                (2)
```

Indeed `div V=−7/6`, `div S=0`, and `S kappa=0`.
The first integration by parts has coefficient
`VH+(div V−1/6)H=(V−4/3)H`, and the second uses the shear identity.
This calculation uses the unnormalized beta, so its infinity residues
remain attached to (2).

Multiply the source-free relation (1) by W and integrate by parts.
Cancelling its additional infinity companion requires `partial_e W=0`.
For such a W,

```
P*W=kappa S[(V−4/3)W].                              (3)
```

Thus this pair of source constructions gives a complete primitive if
one constructs W(u,d) satisfying

```
S[(V−4/3)W]=S[(V−4/3)H].                            (4)
```

The corresponding physical multiplier is `w=H^(-1)W(c,d)`, in agreement
with the separately verified physical outer-E adjoint. A scalar solution
without `W_e=0` leaves the explicit infinity term in (1).

One useful constructive test is whether the right side of (4) is
e-independent on the full actual coefficient cover. If it is, writing
`R(u,d)` for that expression and `Z=partial_d W` reduces (4) to

```
2u partial_u Z+d partial_d Z+9Z=−6R(u,d).
```

This is a weighted Euler equation followed by one d integration.
All operations still have to yield rational/algebraic functions whose
full current descends to the immutable source. If the e derivative is
nonzero, (4) cannot solve the source through this particular paired
annihilator alone; additional full genus-four relations remain available.
No such extra relation is excluded here.
