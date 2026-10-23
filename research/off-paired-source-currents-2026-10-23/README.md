# Off-paired source-bound supplement — UNSOLVED

**No certificate, Lean proof, solve PR, protected verification or acceptance is supplied.** This frozen supplement records explicit source transports and partial currents. Every displayed nonzero remainder, moving-map cochain, finite charge and source-weight cost is retained. None of the partial constructions closes the immutable target.

The target and variable order are checked by `bind_target.py` against `live-instance.rec`: `(X0,X1,X2,Y0,Y1,Y2)`, `A=X0^3Y0^3`, pole parameter one. The required equation remains

```
A*D^2-D*sum(N_i*F_i)+F*(D*div(N)-N(D))=F^2*Q.
```

`Q` may be nonzero. No such legal homogeneous `D,N,Q` has been obtained.

The [original gist](https://gist.github.com/fqlx/2023ba9f5ddc2117c72a03fb9a4c7c55), [first frozen handoff](https://github.com/fqlx/sextics/blob/f7a73cf3346e1da8fded079f16b9e827f218902b/research/off-paired-2026-10-23/HANDOFF-2026-10-23.md), [corrected later handoff](https://github.com/fqlx/sextics/blob/79bd381f50fbcbdf385835982afbac440c99b145/research-handoff/README.md), and [previous constructive supplement](https://github.com/fqlx/sextics/blob/049e28a199a9d9217d23656b1c2d5d007a6b8507/research/off-paired-constructive-2026-10-23/README.md) remain frozen, with their original scopes, corrections and credit. No unavailable Mac file or publication manifest is claimed audited.

## Reproduce without modifying the snapshot

Python 3.12.14, SymPy 1.14.0 and python-flint 0.9.0 were used. The packet needs no credentials, network, Singular, private workspace or separately downloaded research file. Install the pinned packages, then verify and replay:

```
python -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python replay.py --verify-only
.venv/bin/python replay.py --output /tmp/off-paired-source-replay
```

The output directory must be new and outside this snapshot. The runner verifies every frozen hash, copies the packet, and runs the manifest's ordered scripts there. Producer scripts rewrite adjacent JSON receipts, so the source snapshot must stay untouched. The exact replay counts and scopes are listed in `manifest.json` and the adjacent receipts. Some original-source audits are symbolic; the independent Ferrari recovery audit additionally checks a concrete physical fiber at high precision, explicitly marked in its receipt.

`lib/native_source_field.py` contains only the exact arithmetic classes and actual physical source definitions needed by the current replays. `lib/native_source_field.provenance.json` records the original source hashes and extracted line ranges. Unrelated research-producer tails are not imported. `source-provenance.json` records all copied source hashes and the explicit portability changes.

## Direct original-source branch: four elliptic channels and a whole current

On `X0=1`, set `(x,y,z)=(X1,Y0,Y1)`, `p=X2*Y2`,

```
H=1+x^6+y^6+z^6+xyz/2, C=x^3*z/2+xy/3,
Y^2=(H+Cp)^2-4p^6,
beta=-y^3(H+Cp)*dx dy dz dp/(6Y^3).
```

The actual companion uses `u=x^3,w=y^2/x,q=xy`, retaining `q^2=uw`. With `J=H-3zC/2`, its equation is `u^2+(w^3-3z^2/4)u+1+z^6-J=0`. The two varying elliptic quotients and both additional CM elliptic quotients are checked with their complete fixed-C normals. The latter require the full q-cover; the q-even quotient alone does not carry the whole source. Moving CM scale terms are explicit.

The combined phi/current replay proves the literal original-source identity

```
J1=w*dw dz dp/(36*etaB*Y), etaB=2u+w^3-3z^2/4,
beta=dJ1+du dw dz dp*[a0/Y+b0*(H+Cp)*(p+3z/2)/Y^3],
a0=w/(18*etaB^2), b0=z*w/(72*etaB)+w^2/(216*q*etaB).
```

The source-forced CM contact current serves the **entire** second term, including its endpoint motion and the derivative of the forced coefficient. An independent global derivative in the original `(x,y,z,p)` field proves

```
beta=dJtotal+Rphys*dx dy dz dp/Y,
Rphys(1,1,1)=7117189/18729711 != 0.
```

This is a positive whole partial-current identity, not closure. The source maps and checks are in the two companion scripts, the combined phi script, the contact constructor and its independent physical audit.

## Full-P branch: actual finite recovery, CM weights and both cotangents

The upstream scripts independently bind the original sextic to a quartic, the selected Ferrari pair, its plane cubic, the actual section/conic model, and the full-P model. The physical deformation is carried through the **full family**, rather than freezing its missing coefficient. The source-recovery identity applies to a complete weighted pair current; its unnormalized combined recovery factor is `1/4`, with all complement and branch labels retained. Such a pair primitive is not supplied. No primitive is inferred from trace zero.

The maintained model is

```
P=A*m^3+(a/2)*m^2+(D+a/3)*m-V*a^3, h^2=P^2-4R,
A=(R^3+1)/R, D=U^2/4, V^2=4R+R^2/(4D), P_delta=m^2.
```

The rational moving-coordinate cochains from the 2-isogeny and normline chart remain explicit. Depression and scale give `ell=L/S,mu=M/r`, `r^2=R,S^3=R^3+1`, and `y^2=R/(4D)`. The physical normal is already absorbed in `f0=1/(72*y^2*K)`. The conic Cartan and continuity replays verify its entire density normal, including the inverse-branch factor `K`.

The actual zero mark `Q=(a*r/(6S^2),YQ)` satisfies `YQ^2=(4+y^2)*a^6-4`. The source-normalized lambda and nu evaluations use **both** actual second-kind elliptic CM channels. Their exact and spectator-normal cochains are retained. The rational physical current `Jphys=(lambda_n/b)*K_CM` has the full identity

```
dJphys=lambda_n*omegaR*etaA/b+dlog(lambda_n/b)*Jphys.
```

The acceleration cost is nonzero and explicitly weighted. The apparent `hQ=0` pole is removable on the actual cover, while infinity and collision costs remain. `Jphys` is odd under the actual Q-sheet involution; its ordinary trace alone is zero. A source-serving genus-two kernel must supply the matching character before finite push. No such full CM/source intertwiner is claimed.

The exact PF fiber-cochain, actual density/heat and first-jet checks bind the subsequent source row to this physical family. The new two-cotangent current uses the full absolute forms

```
lambda=-X*dlogz, nu=-(X^2/2+ell/3)*dlogz,
d lambda=dell*omega1+dmu*omega0,
d nu=-(ell/3)*dell*omega0+dmu*omega1-dell*dmu/(3Y).
```

For its source-forced coefficients, the complete identity is

```
Omega*(g0*omega0+g1*omega1)
  =dJ_N-Omega*(C_lambda*lambda+C_nu*nu), Omega=dy*dell*dmu.
```

The canonical divergence includes the compulsory `Nbase(K)/K` term. Both remaining second-kind rows are nonzero. The independent physical audit differentiates the entire rational current in `(R,D,a,m)` with every constrained V derivative. No compact row, infinity correction, weight derivative or moving-mark term is deleted.

## What remains open

The two branches above are separate audited partial constructions. They are not asserted to add to a closed source. The remaining task is an actual finite source-serving current for their retained whole residuals, with all finite/infinity, deck, coefficient and normal costs. A closed current must then be transported, traced and homogenized to the original six variables with legal denominator, complex coprimality and the full `F^2*Q` identity. Those obligations remain open.

Credit: `fqlx`'s source reductions and frozen research packets; `benediamond`'s endpoint connection and contact obstruction; `deanodotdotdot`'s subsequent scoped component/coordinate work; the repository's certificate and transport framework. Prepared for `fqlx` with OpenAI Codex algebra, geometry and independent verification agents. Human verification of every AI-generated calculation is not implied.
