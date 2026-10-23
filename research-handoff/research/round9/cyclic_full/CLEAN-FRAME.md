# Actual cyclic Prym: a clean frame, complete primitives, and a free log module

These are exact algebraic improvements to the existing source-bound cyclic
model.  They are not a primitive for the target, and no solve is claimed.

The weighted curve is

```
C=W^6+(5/7)*(h^3+h*t)*W^3+L*h^6+r*h^4*t+t^3/x,
weights(W,h,t)=(1,1,2).
```

The actual cubic-root character, source transport, and positive source sign
are retained; see `independent_physical_source.py/json` and
`/round8/coupled_source/README.md`.  The original basis was
`(Res(h² Omega/C), Res(t Omega/C), Res(t⁴ Omega/C²))`.

## Exact section and reductions

The old weight-eight Jacobian frame had an apparent factor `HolD` of
`L`-degree three and `r`-degree five.  Changing to `theta=∇r omega0` removes it
but introduces a smaller apparent factor; that intermediate transformation
is saved in `theta_frame.py/json`.

The actual construction uses all ten weight-eight monomials.  Their old eta
coefficients have common denominator `Den=5*x²*HolD`.  A short exact Singular
lift proves that their numerator ideal contains `D1*D2`, where

```
D1=27*L²+4*r³*x
```

and `D2` is the second, explicitly saved irreducible discriminant factor.
Only the monomials `h⁶*t,h⁸,W³*h⁵` are needed in the lift.  Their small
polynomial coefficients are saved under `numerator_coefficients` in
`global_eta_frame.pickle`.  Let their combination be `E8`; the new literal
section is `eta_new=Res(E8*Omega/C²)`.  Its old eta coefficient is exactly
`D1*D2/(5*x²*HolD)`.

`global_eta_frame.py` independently checks the polynomial witness, all 100
entries of the new lower Jacobian inverse, the full gauge identity, and all
six holomorphic derivative rows.  The new lower inverse and `N_L,N_r` have
only simple `D1,D2` poles; `N_x` also has a simple `x` pole.  Thus neither old
apparent factor remains.  The packet contains the actual section and exact
Q8 primitives, not merely a change of cohomology coordinates.

The higher reduction uses the full 24-by-36 weight-fourteen Jacobian map.
`global_eta_high.sing` gives explicit lifts

```
E8*C_j = sum_i Q14_i*C_i.
```

The `L,r` lifts are polynomial; the `x` lift has only `1/x`.  In
`global_eta_complete.py`, every identity is checked directly over Q, then
`P8=partial_j E8-div(Q14)` is reduced with the clean lower inverse.  All
three resulting eta connection rows match the independent gauge transform.
The primitive is

```
i_Q14 Omega/C² - i_Q8 Omega/C.
```

For the two holomorphic sections the primitive is `+i_Q8 Omega/C`.
On `h=1`, use `Omega=dW wedge dt` and
`Q_aff=(Q_W-W*Q_h,Q_t-2*t*Q_h)` when taking contractions.  The usual weighted
Euler identity verifies these signs and factors.  Consequently all nine
basis derivatives now have explicit relative primitives with only
`x,D1,D2` parameter poles.  The old selected-square higher inverse's
additional factors `L`, `-L+2r`, and `196L-25` are absent too.

Use **`global_eta_complete.pickle`** for further source/current assembly.
Its matrices use rows as basis derivatives; coefficient columns use the
transpose.  It contains the literal section, all nine primitive corrections,
and the lower inverse as rational polynomial circuits.

## Full logarithmic module

`full_log_module.sing` computes the augmented syzygy module for simultaneous
tangency to `D1,D2,x`.  `full_log_module.py` checks every tangency identity
over Q.  Although Singular returns four generators, the first three satisfy

```
det[V1,V2,V3]=-120050*x*D1*D2.
```

The divisor `x*D1*D2` is reduced, so the Saito determinant criterion proves
that these three fields are a complete free basis of
`Der(-log(x*D1*D2))`.  This completeness conclusion does not depend on
trusting a returned generator count.  The fourth generator is explicitly
checked to be a polynomial combination of the first three.

Contracting the actual clean connection with each field gives a polynomial
three-by-three matrix, with **no denominators**.  Exact tangency quotients,
divergences, matrices, and the generator relation are in
`full_log_module.pickle/json`; use `basis_indices=[0,1,2]`.

The current operator must still retain the physical source density.  For a
coefficient vector `f` along `V`, it is

```
V(f) + (div(V)+V(log H))*f + N(V)^T*f.
```

Dropping `div(V)` or the actual `H=rho*fT/Jac` would change the source problem.
No assertion is made that logarithmic currents exhaust arbitrary meromorphic
currents.  The genuine marked/open-curve extension remains a separate
construction being developed by the other agents.

## Reproduction and scope

The `.sing` input files, exact witnesses, logs, and polynomial packets are
saved in this directory.  Run `schiffer_audit.py`, `global_eta_frame.py`,
`global_eta_complete.py`, and `full_log_module.py` to replay the exact checks;
the scripts use the saved complete input/witness packets and independently
verify their identities.  Native rational polynomial arithmetic makes each
replay take approximately one second.  No repository or external application
was changed.  The original target is still open.
