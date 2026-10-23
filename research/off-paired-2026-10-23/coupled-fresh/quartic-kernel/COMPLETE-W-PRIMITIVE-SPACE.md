# Complete Riemann–Roch space for the normalized actual w source

This is a complete finite construction interface for a rational primitive,
not a completed primitive or a bound on all sextic certificates.

Use the properized actual source with the preferred quadratic infinity
preimage. Its scalar H=K/v has only fold poles of order at most five and is
O(1) at infinity. A remaining constant is served explicitly by the degree
zero polynomial-in-f primitive; it need not be subtracted from the original
normal-function gauge. All fixed finite divisors of H are regular.

Set u=1/a, f=1/v, and let n=L0 and d=w N0 T²; constant nonzero base factors
are irrelevant below. Then f is a nonzero constant times n/d, with

```
deg n=18, deg d=10, deg T=3, deg Ccrit=24.
```

Over the generic coefficient field in i,j,ℓ the curve is the quartic cover
of the w line

```
a⁴+p a³+q a²+r(w)=0,
p=jℓ, q=iℓ²+ℓ+1, r=f(w)ℓ⁶.
```

The numerator n is squarefree and coprime to the fixed denominator factors;
the generic coefficient field excludes their resultant zero loci.

## Genus and the exact allowed primitive divisor

The quartic polynomial in a has three finite simple critical values: zero
and the two values from 4a²+3pa+2q=0. Their pullbacks contribute 18+36=54
simple ramification points. The four simple poles of f (w=0 and the three
N0 roots) contribute 4·3=12. The three double poles at T contribute 3·2=6.
At infinity f has pole order eight, so the quartic cover is unramified,
with four points. Thus total ramification is 72, and Riemann–Hurwitz gives
2g−2=−8+72=64, hence g=33.

The actual source Sdw=−ℓ²H du/6 has at most fourth-order poles at the four
unramified points over each of the 24 folds. At each of the 18 n roots the
ramified a=0 point gives a double pole. All residues vanish: at the folds
by odd Morse parity of H; at a=0 because w−w0 starts with a². At all other
finite points it is regular. Since H=O(1), u=O(w^-2), it is regular at the
four points at infinity.

Consequently ANY rational primitive, if one exists, belongs to L(D), where

```
D=3·(the 96 points above Ccrit)+1·(the 18 a=0 points),
deg D=306.
```

A derivative cannot hide any additional pole in characteristic zero. This
is a necessary divisor statement for the actual source, not a guessed
denominator or trial degree.

## A complete explicit basis

The fractional module allowing only simple poles at the 18 a=0 points,
and no other finite poles, has a basis over the polynomial w ring

```
b0=1, b1=u, b2=(L0/T)u², b3=(L0/T)u³.
```

At a simple pole of f, u is a uniformizer of ramification degree four.
At a double pole of f, u²/T is a unit on each of the two branches, which
explains the necessary division by T. At a zero of f, multiplying u² and
u³ by L0 gives respectively a regular function and an allowed simple pole.
At all other finite places these elements are regular.

Completeness can also be checked by the discriminant. The power basis in
u has discriminant Disc(P)/r^6=Dquartic(r)/r^5. Multiplying its last two
columns by L0/T multiplies the discriminant by (L0/T)^4. Up to a nonzero
base constant the resulting divisor is

```
Disc(b0,b1,b2,b3)=w³ N0³ T² Dnum/L0,
```

where Dnum has simple zeros above the two nonzero quartic critical values.
The valuations are exactly the different valuations 3,3,2,1, reduced by
twice the allowed simple pole at each L0 point. There is no remaining
finite index in the normalization module.

At infinity u~α^-1w^-2 at the four points, with four distinct fourth-root
values of α. The basis grows as w^0,w^-2,w^11,w^9. Their four leading
character vectors are independent, so pole cancellation cannot enlarge
the following polynomial bounds. A complete basis of L(D) is

```
w^k/Ccrit³               (0≤k≤72),
w^k u/Ccrit³             (0≤k≤74),
w^k (L0/T)u²/Ccrit³      (0≤k≤61),
w^k (L0/T)u³/Ccrit³      (0≤k≤63).
```

Its dimension is 73+75+62+64=274, agreeing with
deg D+1−g=306+1−33=274. Differentiating these columns has a one-dimensional
constant kernel and rank 273. Solving the actual source against these
columns, followed by full exact rational identity verification, is a
complete w-only primitive construction attempt. A failure in this space
would concern this particular relative w problem; i,j currents and source
lift changes remain available and the sextic goal would remain open.

No source preimage in this complete space has yet been produced. All 274
columns and the actual source, rather than a smaller selected subset,
must be retained if this construction is used.
