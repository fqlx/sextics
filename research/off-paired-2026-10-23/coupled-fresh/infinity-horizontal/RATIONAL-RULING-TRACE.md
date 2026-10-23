# Rational ruling trace and the full infinity companion

Status: exact source transport, with an uncancelled remainder. No certificate.
The conventions are those of `RULING-NORMAL-FUNCTION.md` and
`../ruling-source/SHEAR-SOURCE-IDENTITY.md`.

Put `delta=D/(2A)`, `W=AX²+CpY²=B(rho²−b²)`, and
`omega=q²dq/J`. Trace the ruling primitive with its source normalization:

```
h=−A rho/(lambda Cp),
Psi=Tr_{rho→−rho}(h beta)/2
   = A b (X dY−Y dX)/W.
```

Thus this source-carrying primitive is rational over the original
coefficient field. This is a trace of a differential, not an assertion
that tracing an arbitrary primitive recovers the original physical source.
Here the exact source identity is checked directly:

```
nabla_SD Psi=q eta_b+d_q F_D,
F_D=B Y b³q/(J W),
SD=partial_D+(D/(2A))partial_C.
```

There is a second normalizer-preserving translation

```
VE=partial_E+(E/(2Cp))partial_T,
VE Q=Y, VE rho=VE lambda=0.
```

Its exact source identity is

```
nabla_VE beta=d_q F_E+(lambda/rho)(delta eta_b+3omega),
F_E=lambda[XJ+2Cp aY²]/[2B rho J(b+rho)].
```

The scalar derivative is **VE(c_inf)**, rather than a partial E derivative
at fixed T. It satisfies
`VE(c_inf) omega_inf=(3lambda/rho)omega`. Consequently

```
nabla_VE beta_hat=d_q F_E+(lambda delta/rho)eta_b
                  −c_inf nabla_VE omega_inf.
```

The rational traced identities retain the same infinity companion. Write
`g=3AE/Cp`. Then

```
Psi_hat=Tr(h beta_hat)/2=Psi+g omega,
nabla_VE Psi=d_q F_Er−(A/Cp)(delta eta_b+3omega),
F_Er=A b[XJ+2Cp aY²]/(2Cp J W),
eta_b=f nabla_VE Psi_hat−f g nabla_VE omega+fiber-exact,
f=−2Cp/D.
```

These identities do not remove the third-order second-kind infinity poles
of the ruling primitive. They remove its infinity residues.

For the physical lift `Y` of `VE`, with coefficients `(alpha,u,v)` as in
`actual_ruling_adjoints.py`, the scalar connection terms are

```
c_Psi=−2u+2v/3, c_omega=−alpha+2v.
```

Let `ME` be the first weighted adjoint of the actual E-source direction:
`ME=div_mu(V_Esource)+c_eta,E`. After both integrations by parts the
finite and infinity terms are

```
G_Psi=−div_mu(f ME Y)−f ME c_Psi,
G_omega=div_mu(f g ME Y)+f g ME c_omega,
G_Psi Psi_hat+G_omega omega.
```

Returning to the unnormalized rational trace gives the useful exact
bookkeeping identity

```
G_Psi Psi−(6A/D)ME omega.
```

Indeed `Yg=VEg+(c_Psi−c_omega)g` and `VEg=3A/Cp`.
In the T/SD transport the analogous raw infinity coefficient cancels,
because `SDg=0`. Therefore a proposed interpolation between these two
source transports has to cancel both its ruling coefficient and this
explicit infinity coefficient.

`verify_rational_ruling_trace.py` checks nine exact symbolic groups,
including the two translation numerators, rational trace, both exact
potentials, and the rational infinity normalization. The physical
double-adjoint residue in `actual-ruling-adjoints.json` remains nonzero;
its value divided by `h=−kappa` at `R=S=z=k=1` is `241/9`.
Equivalently, the surviving beta coefficient divided by `kappa` is
`−241/9`, matching the positive `g=div_mu(kappa M_T VD)` convention
used in `../ruling-source/physical-source-adjoints.json`.

`verify_ruling_infinity_adjoints.py` adds two exact physical checks of
the connection character and companion adjoint. Its first E adjoint is
`ME=−10/3` at the same point, so the raw omega remainder is `+80` there.
