# Generic charged scalar-route obstruction at the B=0 boundary

This is a statement about the displayed charged scalar equation over
`K=QQ(eta,V,s)` or `C(eta,V,s)`, with `c=5/7`. It is not a statement about a special invariant
level and is not an unrestricted certificate obstruction. All coefficients
below are independently extracted and checked by `resonance_obstruction.py`.

An independent parent replay is recorded in
`independent_contracted_audit.py` and `independent_contracted_audit.json`.
It bypasses the compact charge, A0 and C0 formulas entirely: it substitutes
`p=nu^2*f(V)/(s*q_s0)` into the pinned contracted `Bred/Cred/rhsred`
equation, extracts formal coefficients of f,f',f'', proves all lower
nu-orders vanish, and checks that the first surviving coefficients are
exactly T4 squared and R0. That replay passed in 9.2 seconds.

Write `delta=Y/(q*Delta0)`, `k=1+V^6+s^2`, `M=3k/q`. The equation is

```
[(delta-a)^2-A0*(delta-a)+C0]u=Bsrc,
a=(delta(log s)-2delta(log M))/3,
Bsrc=-(3/5) M*T*Rnum0/(s*Delta0^3).
```

## First place: s=0

The divisor is invariant: `Y_s` is exactly divisible by `s`. On its generic
point put `mu=(delta s/s)|s=0` and let `delta0` be the induced derivation on
`QQ(eta,V)`. Since `M|s=0=1`, `a|s=0=mu/3`. Moreover `A0=27,C0=162` there.
The source has precisely one s-pole, with leading coefficient

```
R(eta,V)=55566*(2V^6*eta-V^4+eta)/(125*V*(eta*V^2-1)^3).
```

Thus if a rational u has leading term `s^n*w(eta,V)`, its leading operator is

```
L_n=[delta0+(n-1/3)mu]^2-27[delta0+(n-1/3)mu]+162.
```

## Second place: nu=9eta+14=0 inside s=0

Direct extraction gives

```
delta0(nu)=9nu-9nu^2/5,
delta0(V)=C(V)/nu+O(1),
mu=3C(V)*(V^6-1)/(V*(1+V^6)*nu)+O(1),
C(V)=-475V^2/[3(14V^2+9)].
```

For a pole `n=-m`, put `a=3m+1` and

```
T_a=C(V)[d/dV-a*(V^6-1)/(V*(1+V^6))].
```

For any integer nu-order `l` and nonzero rational leading coefficient f(V),
the nu-leading term of `L_-m(nu^l f)` is `nu^(l-2)*T_a^2 f`. The
`delta0(nu)` term contributes only less singular orders, and the terms with
27 and 162 likewise cannot change this leading term.

At a root of `1+V^6`, the indicial exponents of `T_a^2` are `a/3,a/3+1`.
For every integer m they are nonintegers. Therefore `T_a^2` has no nonzero
rational homogeneous solution. This proves that a rational homogeneous
solution of `L_-m` cannot exist either: take its finite nu-valuation and
apply the leading term. Since the source has s-order -1, a rational u cannot
have an s-pole of order greater than one. It cannot have s-order >=0 because
the operator preserves s-order. Hence it must start `u=s^-1*w+...`.

For m=1, the right side R has nu-order zero and is nonzero. The same
homogeneous-kernel argument forces `w=nu^2*f(V)+...`, and gives

```
T_4^2 f = R0,
R0=4500846*(28V^6+9V^4+14)/(125*V*(14V^2+9)^3).
```

The compact-charge gauge requested in the parent task does not change the
obstruction. Here `g|s=0=1/(3c eta)` is a unit with `g^-1=-10/3` at nu=0.
Its additional charge `delta0(eta)/eta` is O(nu), so the gauged leading
operator is the same T4, and the right side is merely `(-10/3)R0`.

## The last rational ODE has no solution

At each of the six roots of `1+V^6`, R0 is regular, C is a unit, and the
indicial exponents are `4/3,7/3`. An integer-order rational solution must
therefore vanish to order at least two at each root.

At V=0, `C~const*V^2`, and the indicial factors on a term V^j are
`(j+4)(j+5)` with exponent shift +2. Since R0 has a simple pole, f can have
at most a pole of order five. At infinity, C tends to a nonzero constant;
the factors for growth V^j are `(j-4)(j-5)` with exponent shift -2. Since
R0=O(V^-1), f grows at most as V^5.

At a zero of `14V^2+9`, C has a simple pole and R0 a pole of order three.
The indicial factor is `j(j-2)` with exponent shift -4. A pole of f would
give a strictly larger pole on the left and is impossible. At every other
finite point outside V=0, all coefficients are regular with nonzero leading
coefficient, so f cannot have a pole.

Consequently V^5*f is a polynomial of degree at most ten. It must be
divisible by `(1+V^6)^2`, of degree twelve. This forces f=0, contradicting
the nonzero R0. Thus the generic rational scalar equation has no solution.

The independent finite searches in this folder are diagnostics only; this
argument uses exact coefficient identities and valuation bounds, not their
negative modular results. Finite algebraic extensions cannot supply a
solution to this same linear equation either, since normalized trace would
produce a rational solution in characteristic zero. This trace observation
does not enlarge the scalar route into a necessary condition for arbitrary
legal certificates.
