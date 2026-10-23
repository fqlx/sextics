# Trace-zero quartic integration interface for the actual K source

This retains the actual physical cover and multiplier. No rational primitive
for the full remaining source is yet supplied.

Write

```
P=a⁴+p a³+q a²+r,
p=jℓ, q=iℓ²+ℓ+1, r=f(w)ℓ⁶, f=1/v(i,j²,w),
H=K/v=Kf.
```

The source coefficient in the orientation dℓ∧dw∧di∧dj is

```
S=K f_w ℓ²(a²+p a+q)/(6P_a).
```

Because a²(a²+p a+q)=−r and a_w=−f_wℓ⁶/P_a,

```
S=−(ℓ²/6) H ∂w(1/a)
 =∂w[−ℓ²H/(6a)]+ℓ²H_w/(6a).
```

The last residual is retained. H is the full explicit PN+Ctot from the
actual-source scalar construction, not a polynomial replacement or trace.

## Exact rank-three connection

Tr(1/a)=0, since the quartic has zero linear coefficient. The entire source
therefore lies in its trace-zero rank-three algebraic differential module.
Use the basis

```
E1=a+p/4,
E2=a²−(p²−2q)/4,
E3=a³+(p³−3pq)/4.
```

`quartic_w_connection.py` computes Γ by exact polynomial modular inversion:
∂r Ej=Σi Γij Ei. Then ∂w Ej=f_wℓ⁶ Σi Γij Ei. All nine generic entries are
saved explicitly in `quartic-w-connection-results.json`; no marked point or
finite-field specialization is used.

The exact vector of 1/a is (−q,−p,−1)/r. Consequently the full source vector
is simply

```
−(ℓ²/6)H f_wℓ⁶ [(∂r+Γ)(−q,−p,−1)^T/r].
```

A rational coefficient solution Y_w+Γ_wY=S gives an actual current
−(Σi YiEi)dℓ∧di∧dj. The module formulation keeps all quartic sheets.

## A useful proven serving target

If source-preserving lift changes can put the ACTUAL H into polynomial
form H=Σn hn fⁿ with hn in the base coefficient field, the remaining source
has an explicit rational primitive of every degree. Indeed substitute
f=−a²(a²+p a+q)/ℓ⁶ and integrate

```
B_a=ℓ² H(f(a))/(6a²).
```

The n=0 term is proportional to a^-2; all n≥1 terms are polynomials in a.
There is never an a^-1 term. The primitive is

```
B=ℓ²/6 [−h0/a
  +Σn≥1 hn (−1)^n ℓ^(-6n) ∫a^(2n−2)(a²+p a+q)^n da].
```

Then B_w=S and −B dℓ∧di∧dj is the four-form current. This sufficient target
does not say the actual H has that form. Its full w dependence must still
be served. The script checks n=0,…,4 and the all-degree formula follows
from the nonnegative exponent 2n−2 for every n≥1.

## Direct cancellation of the artificial fold poles

At a simple physical fold choose a Morse coordinate s²=v−vc(i,J). Then

```
A=∂i|s−vc_i/(2s)∂s,
B=∂J|s−vc_J/(2s)∂s,
Z=(vc+s²)/(2s)∂s.
```

These preserve parity. In the ORIGINAL CRT lift, the initial h,F,G are analytic one-form moments
divided by v_s, so only their s^-1 term is negative. Their order-two
operators, and the order-three operator on the analytic Hpot, give R with
only odd negative powers down to s^-5. Since H_w dw=R dv/v², H has only
negative powers s^-3,s^-1. This uses the actual fully differentiated scalar
identity; no pole at a fold is omitted.

This order-three bound does **not** survive arbitrary exact-moment changes.
In particular, the cubic polynomial-moment properization changes H by
L3 QH. For QH=q0+q1s+…, the leading cubic symbol gives
L3 QH=3 sigma3 q1/s^5+O(s^-3), generically nonzero. Thus after FULL initial
moment properization and the preferred quadratic infinity preimage, H may
have the odd principal powers s^-5,s^-3,s^-1. The resulting source has pole
order four. The one-level formulas below apply to the original order-three
case; use the complete finite Hermite recursion for the properized source.

But u=1/a depends on s only through v, so u is even and u_s=O(s). Therefore
the actual source Sds=−ℓ²H u_s ds/6 has only a double pole and ZERO residue.
Only the s^-3 coefficient of H contributes a pole at all. If
H=h_-3/s³+h_-1/s+O(1), u=u0+u2s²+O(s⁴), a local source primitive is

```
Bfold=ℓ² h_-3 u2/(3s).
```

This is a rational Hermite current on the quartic module, not a proposal
to drop H's s^-1 term. For the global squarefree critical polynomial C,
Γ_w is regular and vanishes modulo C. If S=n/C² plus lower poles, choose
the vector t modulo C by t=−n(C')^-1 modulo C. Then t/C removes the double
pole; the remaining simple coefficient vanishes by the zero-residue
argument. The inverse is a finite algebraic modular inverse or adjugate.
Other boundary and compact terms remain to be served. This can avoid the
larger task of making H itself regular at every fold.

A lighter compressed current avoids even the rank-three vector
interpolation. Let qinv(w) be the polynomial remainder of the scalar
inverse of f_ww modulo C. It exists at every simple fold. Then

```
Bfold=+(ℓ²/6) H (f_w)² qinv ∂f(1/a),
Sreg=−(ℓ²/6)H f_w ∂f(1/a)−∂w Bfold.
```

Sreg is the actual retained source after this explicitly supplied current;
it has no poles at the smooth simple folds. To check the complete principal
part, use t=w−c, H=A/t³+B/t²+O(t^-1). Put
f_w=f2 t+f3 t²/2+…, where f2=f_ww(c) and f3=f_www(c).
The Morse zero-residue identity is **B=−A f3/(2f2)**. The source principal part is
−ℓ² A f2 u_f(c)/(6t²), while Bfold has principal
+ℓ² A f2 u_f(c)/(6t). Differentiating Bfold cancels the full double pole.
The simple part is zero, with all regular jets kept. The script checks
these four identities with independent symbolic local coefficients.

This formula uses qinv modulo C rather than the rational function
1/f_ww, thereby introducing no extra finite inflection divisor. If desired,
the ordinary polynomial coefficient parts of the rank-three vector Bfold
can be subtracted explicitly; this preserves all fold principal parts and
limits its growth at infinity. The resulting Sreg still retains every
fixed-boundary and infinity contribution. No averaging or projection of H
has been made.

For the properized source with fourth-order fold poles, the exact procedure
is still finite and deterministic. In the trace-zero coefficient module,
Γw is analytic and vanishes modulo C. For each successive remaining pole
order m=4,3,2, let n=(C^m S) mod C and choose

```
t=−n [(m−1) C']^-1 mod C,
Y_m=t/C^(m−1).
```

Subtract (∂w+Γw)Y_m and continue. At the end the simple coefficient is zero
by the Morse parity/residue argument. The actual current has denominator
at most C³ in this module. This is a complete pole reduction, not a choice
of arbitrary polynomial trial degrees. The remaining source after all
three steps, including all boundary and infinity terms introduced by the
global rational representatives, is retained for further integration.

The generic algebraic connection, trace-zero property, full source identity,
discriminant and polynomial serving checks are exact. They do not establish
the missing source integration, original certificate, Lean verification,
protected CI or acceptance.
