# Infinity-complete annihilator reconstruction

This is a constructive reduction with an unsolved source equation.  It does
not omit the ruling residues, the infinity companion, or the second-kind pole
of the literal beta.  The actual physical lifts and density adjoints are in
`../physical_source_adjoints.py`.

Put `kappa=1/K`, `n=(2Cp/D)kappa`, and write the two universal directions as

```
S=partial_D+D/(2A) partial_C,
W=partial_E+E/(2Cp) partial_T.
```

The source identities, modulo their explicitly retained rational fiber
primitives, are

```
S beta = -K q eta_b,
W beta = L eta_b + M omega_inf,
L=lambda D/(2A rho),  M=W(c_inf)=3lambda/(2B rho c0).
```

The literal identity `partial_E eta_b=partial_T(q eta_b)` therefore gives

```
P beta = partial_E(n M omega_inf) + fiber-exact,
P=partial_E o nW + partial_T o kappa S.
```

Equivalently, with `beta=beta_hat+c_inf omega_inf`, the complete relation is

```
P beta_hat + Q omega_inf = fiber-exact,
Q=partial_E o n c_inf W + partial_T o kappa c_inf S.
```

All multiplication/operator orders in these equations are intentional. Since
`S(c_inf)=0` and `W(c_inf)=M`, they imply the exact Ore identity

```
Q=P o c_inf - partial_E o (n M),
Q*=c_inf P* - n M partial_E*.
```

Thus a multiplier matching `g beta_hat+g c_inf omega_inf` must satisfy both
`P* w=g` and `Q* w=c_inf g`.  In the corresponding actual weighted outer-E
convention this is a paired scalar system: the finite source match and the
outer-E kernel equation. Solving only the finite equation is insufficient.

## Explicit integrating factor on the actual coefficient locus

Use `R=r^2,S=s^2,k^6=RS` and

```
A=1+R, B=1+S, C=k/3, D=zk/2, E=z/2, T=1+z^6,
delta=3RSz^6-3RS-8Rz^6+R-Sz^6+2S,
mu=(1/108)R^(-5/6)S^(-5/6)dR dS dz.
```

After the finite coefficient cover normalizing A,B,T, put

```
c=C T^(-1/3)(AB)^(-1/3),
d=D T^(-1/6) A^(-2/3) B^(-1/6),
e=E T^(-2/3)(AB)^(-1/6).
```

Direct differentiation gives

```
det d(log c,log d,log e)/d(R,S,z)
 =delta/(36RSzABT).
```

The physical E lift fixes c,d and satisfies `V_E(e)=e/E`.  The holomorphic
form transforms as `eta_b=L_b eta_norm`, with
`L_b=T^(-1/6)A^(-1/6)B^(-2/3)`.  Consequently the normalized source density is

```
Hsrc=4 T^(4/3) A^(11/6) B^(5/6)/(z k delta).
```

In the source-agent interpolation convention, let `f` weight the T/shear
route and `u=1-f` weight the E/W route.  Its complete infinity coefficient
vanishes exactly when

```
V_E(u)+hE u=0.
```

The rational logarithmic identity `V_E(log Hsrc)=hE` is verified exactly.
Thus every local solution on this coefficient cover is

```
u=Hsrc^(-1) W(c,d).
```

This is an algebraic integrating factor, with no logarithmic primitive or
assumed constancy of the physical Jacobian.  The remaining actual finite
source condition is

```
D_S[V_T(u)+hT u]=D_S(hT),
D_S(h)=V_S(h)+(div_mu V_S+V_S(log kappa))h.
```

This is a genuine equation for W(c,d), required as an identity on the full
three-dimensional physical coefficient cover. No W satisfying it has yet
been constructed.

## Explicit two-variable operator

Write `w0=Hsrc^(-1)`, `theta_c=c partial_c`, `theta_d=d partial_d`, and

```
t1=-1/(3T), t2=-1/(6T),
s1=D/(2AC), s2=1/D,
eta=hT+V_T(log w0),
chi=div_mu V_S+V_S(log kappa)+V_S(log w0).
```

Then the remaining equation is `w0 O(W)=D_S(hT)`, where the actual operator
coefficients, including all physical derivatives, are

```
O =s1 t1 theta_c^2 +(s1 t2+s2 t1)theta_c theta_d+s2 t2 theta_d^2
  +(V_S(t1)+chi t1+eta s1)theta_c
  +(V_S(t2)+chi t2+eta s2)theta_d
  +V_S(eta)+chi eta.
```

The coefficients may depend on all three physical coordinates.  Their
dependence must not be frozen while solving for W.  This expression gives a
complete source reconstruction for this particular annihilator/interpolation
channel; it is not an exclusion of additional genus-four currents.

`verify_normalized_kernel.py` checks the determinant, the physical E action,
the holomorphic-form character, the integrating factor, and the full source
density exponents using exact symbolic arithmetic.

## Actual remaining forcing and the broader current mechanism

The independent third-order Fraction calculation in
`evaluate_reduced_mixed_derivative.py` retains all derivatives of the
normalizing factors `D/d` and `E/e`.  At `R=S=z=k=1` it gives

```
Hsrc=-32/3,
(Tfield-4/3)Hsrc=832/27,
S_normalized[(Tfield-4/3)Hsrc]=30848/27,
partial_e S_normalized[(Tfield-4/3)Hsrc]=3138560/81.
```

Thus this displayed source does retain e dependence; it cannot simply be
replaced by an e-independent forcing while constructing W. This is a gap in
the single paired-annihilator channel, not an exclusion of other currents.
The actual mixed derivative, eight normalized action checks, and the complete
local values are saved in `reduced-mixed-derivative-results.json`.

The independent finite-residue differential chi supplies three source-current
generators and additional compact directions. Their literal fiber primitives
and complete Green reconstruction are in `CHI-THREE-OPERATOR-CURRENTS.md`.
The complete genus-four compact RR mechanism is in
`../../genus4-gm-independent/COMPLETE-RR-CONNECTION.md`.
