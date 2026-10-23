# Full-family shear identity and the physical source

Status: constructive identity established; **no primitive or certificate**.
All statements concern the actual source presentation in
`../infinity-horizontal/RULING-NORMAL-FUNCTION.md`. No infinity term is
discarded here.

Write

```
Q=Aa²+Bb²+Cq²+Daq+Eq+T, ab=q³,
Cp=C−D²/(4A), X=a+Dq/(2A), Y=q+E/(2Cp),
rho²=(E²/(4Cp)−T)/B, lambda²=−A/Cp,
J=a Q_a−b Q_b, eta_b=b dq/J,
Rlog=(Y−lambda X)/(Y+lambda X),
beta=−(b−rho)/(2rho) d_q log Rlog.
```

The universal parameter direction

```
V=partial_D+(D/(2A)) partial_C
```

keeps `A,B,Cp,E,T,rho,lambda,c0,c_inf` fixed and has `VQ=qX`.
At fixed q its lift to the curve is

```
V a=−a qX/J, V b=b qX/J.
```

Put

```
L_V=V log Rlog
   =−2lambda Y (V a+q/(2A))/(Y²−lambda²X²),
h_V=−(b−rho)L_V/(2rho).
```

Here `log` abbreviates its rational logarithmic derivative; neither
`L_V` nor `h_V` contains an actual logarithm. A literal identity is

```
nabla_V beta = d_q h_V − [lambda Cp/(A rho)] q eta_b.       (1)
```

The independent Fraction/Cartan verifier simplifies the same exact
potential to

```
h_V=lambda Cp Y b²q/[A rho J(b+rho)].
```

To check it, differentiating the displayed product defining beta gives

```
nabla_V beta−d_q h_V
 = [b_q L_V−(Vb) (d_q log Rlog)]dq/(2rho).
```

Substitute `a_q=(−aQ_q−3q²Q_b)/J`,
`b_q=(bQ_q+3q²Q_a)/J`, `Q_a=2AX`, and
`Q_q=2CpY+(D/A)AX`. The norm relation cancels the cubic terms;
the remaining numerator is `bq[AX²+CpY²]/A`. Finally
`AX²+CpY²=B(rho²−b²)` cancels the ruling denominator and yields (1).
The identity holds for all D, including the physical value D=zk/2.

For `beta_hat=beta−c_inf omega_inf`, the complete identity is

```
nabla_V beta_hat
 =d_q h_V−[lambda Cp/(A rho)]q eta_b−c_inf nabla_V omega_inf. (2)
```

Thus one may equivalently use `nabla_V beta` in (1): its finite
residues and its infinity residues are constant in V, so its derivative
has no residues. This retains the third-order second-kind pole of beta
at infinity. It does not replace beta by a differential without that pole.

The actual source is `tau=−nabla_T(q eta_b)`, equivalently
`tau=−nabla_E eta_b`, with the physical base density
`mu=dr dk dz/(9r)`.
Writing `kappa=A rho/(lambda Cp)`, identity (1) gives

```
q eta_b=−kappa nabla_V beta+fiber-exact.
```

Writing `d=kappa c_inf=3AE/(2B Cp c0)`, which is T-constant, the full
normalized identity yields the literal source formula

```
tau=nabla_T(kappa nabla_V beta_hat)
    +d nabla_T nabla_V omega_inf−d_q[nabla_T(kappa h_V)].
```

Thus the infinity companion is explicitly present even in the
second-derivative expression.

## Torus and scaling compatibility

For the norm-torus field
`Xtor=u(a partial_a−b partial_b)+v(a partial_a+b partial_b+(2/3)q partial_q)`,
put `wa=u+v, wb=−u+v, wq=2v/3`. Under its simultaneous coordinate change
and inverse coefficient change, weights are

```
(a,b,q)=(wa,wb,wq),
(A,B,C,D,E,T)=(−2wa,−2wb,−2wq,−wa−wq,−wq,0),
(X,Y,rho,lambda)=(wa,wq,wb,wq−wa).
```

Consequently the relative differential beta is exactly invariant.
It is also exactly invariant under common scaling of all Q coefficients.
The separate terms `c_inf` and `omega_inf` are invariant under these
operations. Thus passage from a universal coefficient direction to its
physical tangent/torus lift introduces no scalar multiple of beta;
the ordinary Cartan fiber-exact correction remains present.

## Physical adjoint, with its remaining source

The complete rational lifts and adjoints are recorded, independently
derived, in `../infinity-horizontal/actual_ruling_adjoints.py` and
`actual-ruling-adjoints.json`. Use
`R=r²,S=s²,k⁶=RS`; then
`mu` is a constant multiple of `R^(−5/6)S^(−5/6)dR dS dz`.
For the T lift `VT` and its torus coefficient `vT`, the first integration
by parts leaves

```
hT q eta_b,  hT=div_mu(VT)+2vT.
```

It is nonzero. For the physical shear lift `VD`, the second step leaves

```
g beta,
g=div_mu(kappa hT VD),
g/kappa=VD(hT)+hT div_mu(VD)+(hT/2)VD(log(kappa²)).
```

The square used here is rational:

```
kappa²=A[T−E²/(4Cp)]/(B Cp).
```

This scalar too is nonzero. It is a residual actual source, not an
exclusion of other currents. In terms of beta_hat the residual retains
`g beta_hat+g c_inf omega_inf`, with both finite ruling residues and
infinity residues visible. A valid solution still has to cancel this
residual using the full physical connection or additional geometric data.
