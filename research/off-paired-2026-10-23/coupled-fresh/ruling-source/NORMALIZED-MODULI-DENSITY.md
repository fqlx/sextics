# Normalized moduli and a source-carrying outer-E integrating factor

Status: exact coordinate and weighted-adjoint identities; no primitive or
certificate. All fractional powers below are on a finite algebraic cover,
with compatible choices. A completed primitive there would still need trace
descent and the original certificate side conditions.

For `Q=Aa^2+Bb^2+Cq^2+Daq+Eq+T`, `ab=q^3`, set

```
a=(T/A)^(1/2) a', b=(T/B)^(1/2) b',
q=T^(1/3)(AB)^(-1/6) q'.
```

Then the norm equation is unchanged and `Q/T` has coefficients

```
1,1,c,d,e,1,
c=C T^(-1/3)(AB)^(-1/3),
d=D T^(-1/6)A^(-2/3)B^(-1/6),
e=E T^(-2/3)(AB)^(-1/6).
```

For the actual parameters `R=r^2,S=s^2,k^6=RS,z`, put
`A=1+R,B=1+S,T=1+z^6,C=k/3,D=zk/2,E=z/2` and

```
Delta=3RS z^6-3RS-8R z^6+R-S z^6+2S.
```

The exact logarithmic coordinate Jacobian is

```
det partial(log c,log d,log e)/partial(R,S,z)
   =Delta/(36RS zABT).
```

The actual base density and canonical differential scale as

```
mu=dR dS dz/(108k^5),
eta_b=L eta'_b, L=T^(-1/6)A^(-1/6)B^(-2/3),
epsilon=partial_E e=T^(-2/3)(AB)^(-1/6).
```

Consequently the exact source, including its full density, is

```
-partial_E(eta_b) mu
 =-H partial_e(eta'_b) dc dd de,
H=4 T^(4/3)A^(11/6)B^(5/6)/(z k Delta).
```

This formula retains the varying curve differential. It does not integrate
the source merely by integrating its scalar density.

Let `VE` be the actual lift of the universal coefficient direction
`partial_E` (not the centered translation `partial_E+E/(2Cp)partial_T`).
Its torus/scaling scalar on eta_b is
`c_eta=-alpha-u+5v/3`. Write
`hE=div_mu(VE)+c_eta`. Direct symbolic differentiation gives

```
VE(H^(-1))+hE H^(-1)=0.
VE(c)=VE(d)=0,
VE(e)=epsilon.
```

Thus the complete local solutions of the outer-E adjoint constraint have
the form `w=H^(-1) W(c,d)`, allowing the appropriate constants of the
algebraic coefficient field. This removes one PDE from the paired
normal-function correction problem. It does not solve the remaining
adjoint equation, and the infinity companion must still be matched.

`verify_normalized_moduli.py` checks the coordinate/Jacobian/source density
and the actual physical adjoint identity by rational logarithmic
derivatives; no floating point or logarithmic primitive is used.
