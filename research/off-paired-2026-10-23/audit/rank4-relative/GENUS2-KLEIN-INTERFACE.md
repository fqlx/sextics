# Exact relative kernel interface and both isomorphism branches

For the common genus-two family f(t)=(H+Ct)^2-4t^6, define

```
F2(p,q)=2H^2+2HC(p+q)+2C^2pq-8p^3q^3,
Kp=(Zp+Zq)/(2Zp(p-q)),
Bpq=(F2+2ZpZq)/(4(p-q)^2ZpZq).
```

With Zq^2=f(q), the bidifferential coefficient identity is

```
Bpq=partial_q(Kp)-2p q^3/(ZpZq)-4q^4/(ZpZq).
```

It follows from
`F2-2f(q)-(p-q)f'(q)=-8q^3(p-q)^2(p+2q)`.
This explicitly retains both second-kind components. In a literal exterior
current, the q-part of d(Kp dp) is **minus** partial_q(Kp) dp wedge dq.
The coefficient derivative above uses the customary tensor-bidifferential
convention and must not be substituted with the opposite exterior sign.

For the two actual parameter pairs (H,C) and (D,B), let
`r=HB/(DC)` and `mu=B^3H^2/(D^2C^3)`. Then

```
r^3D=mu H, r^2B=mu C,
f_endpoint(rq)-r^6 f_background(q)
  =(1-mu^2)(H+Crq)^2.
```

Thus both signs mu=+1 and mu=-1 give an explicit relative curve isomorphism.
The sign symmetry (H,C)->(-H,-C) leaves the defining polynomial unchanged.
For the homogeneous actual background B=-w^3z/2, the union of these two
obvious branches is the degree48 background support

```
(8D^2C^3+w^9z^3H^2)(8D^2C^3-w^9z^3H^2)=0.
```

Either branch is a valid candidate support on its own. All varying-scale
terms, discriminant intersections and the physical source must still be
handled. A relative isomorphism, a relative bidifferential, or the exact
closed form d(tau) does not prove that a nonzero proper H20 residue extends
or matches the target. The final current/certificate remains unsolved.

On either parameter branch the endpoint point P=p/r and background point q
are independent. The curve isomorphism identifies their ambient curves; it
does not identify these two points. The diagonal P=q is a further divisor,
and its poles and residues must be retained in any two-point kernel.

`verify_genus2_klein_interface.py` checks six exact symbolic groups.
