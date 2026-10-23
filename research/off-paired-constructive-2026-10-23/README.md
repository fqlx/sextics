# Off-paired constructive supplement — UNSOLVED

This is a small constructive supplement. It is not a solve submission. The [original reproduction packet](https://gist.github.com/fqlx/2023ba9f5ddc2117c72a03fb9a4c7c55), [first frozen handoff](https://github.com/fqlx/sextics/blob/f7a73cf3346e1da8fded079f16b9e827f218902b/research/off-paired-2026-10-23/HANDOFF-2026-10-23.md), and [later frozen handoff](https://github.com/fqlx/sextics/blob/79bd381f50fbcbdf385835982afbac440c99b145/research-handoff/README.md) remain unchanged, with their original claims, corrections and credits. No original Mac-only unpublished file is included or claimed audited.

The immutable target is in `live-instance.rec`. The full witness equation remains

```
A*D^2-D*sum(N_i*F_i)+F*(D*div(N)-N(D))=F^2*Q.
```

`Q` may be nonzero. No such witness or proof is supplied here.

## Reproduce

Python 3.12.14, SymPy 1.14.0 and python-flint 0.9.0 were used. No Singular, private credentials or old workspace paths are required. Preserve the directories below. Run in a disposable copy because producer scripts rewrite their adjacent JSON receipts; the published source packet and original receipts must remain frozen.

```
python -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python bind_target.py
.venv/bin/python root_CM_projector_and_original_source.py
.venv/bin/python fresh-algebraic-construction/actual_CM_Green_concomitants.py
.venv/bin/python fresh-algebraic-construction/actual_full_source_dual_Green_packet.py
.venv/bin/python source-incidence-correspondence/actual_CM_projector_source_seed.py
.venv/bin/python source-incidence-correspondence/actual_full_CM_repair_descent.py
.venv/bin/python endpoint-adjoint-new/ward/actual_full_t_seed_CM_projector_literal_audit.py
.venv/bin/python endpoint-adjoint-new/ward/actual_original_field_Y_CMdesc_literal_audit.py
.venv/bin/python fresh-algebraic-construction/actual_Y_CM_Green_weight_repair.py
.venv/bin/python fresh-algebraic-construction/native_original_Y_CM_Green_raw.py
.venv/bin/python fresh-algebraic-construction/native_original_endpoint_current_audit.py
.venv/bin/python root_current_to_certificate_lift.py
.venv/bin/python independent_current_to_certificate_lift_audit.py
.venv/bin/python fresh-global-construction/ONE_actual_Psi_assembled_current.py
.venv/bin/python root_ONE_current_literal_audit.py
```

The endpoint audits read `endpoint-adjoint-new/native_q_connection.json`; it is included. That array's complete normal and exact-fiber identities are checked by the audits, rather than inferred from a stored rank. Each replay's scope is stated in its JSON. A passed partial-current audit is not a certificate.

Before rerunning scripts, verify the frozen file hashes from this directory:

```
python - <<'PY'
from pathlib import Path
import hashlib,json
m=json.loads(Path('manifest.json').read_text())
for name,want in m['files'].items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==want['sha256'], name
print('PASS',len(m['files']),'frozen file hashes')
PY
```

## What is established

The physical source is the entire original signed-channel density, not a single channel:

```
beta=-(U/W-1)*eta*dU*dR*thetaH/108,
eta=dt/rho, rho^2=2t^3-1,
U=x^3+y^3, W=x^3-y^3, t=xy/z^2, R=rho*z^3.
```

The Green packet includes every physical parameter normal. The CM projectors use actual points on `Y^2=X^3-1`, and the complete source-weighted trace descends to the original field. The original-field audit differentiates the nonconstant amplitude, every source and CM factor, the endpoint H and C dependence, and the rational fiber cochains. Its remaining four compact components are nonzero.

The later Green weight repair serves one specified weight-derivative component and explicitly retains further packets. The native FLINT auditors now differentiate the whole Y + descended CM + Green current directly over the original rational field, with no sequential main-term substitution. The complete rational obstruction is retained and is nonzero. No full cancellation is claimed.

The `ONE_actual_Psi_assembled_current` audit proves that an earlier three-piece prefix collapses literally to ordinary integration by parts plus an exact current. Its retained coefficient is nonzero. This prevents treating the prefix as a source-serving construction.

## Exact conditional extraction

The extraction applies to a hyperelliptic-odd current with arbitrary rational coefficient functions `q_vector(x,y,z,p)` and `s(x,y,z,p)`. This `q_vector` is not the certificate pole parameter; the immutable problem here has pole parameter one. Higher odd powers of Z in a denominator are absorbed using the endpoint relation `Z^2=f`.

Write `p=e*b`, `R=e^6+b^6`, `Z=e^6-b^6`, `L=H+Cp`, `F=R+L`, and `d=div(q_vector)-partial_p(s)`. The general extraction verifies

```
dF(v)=A,
div(v)=6E/Z^2+F*Qstar,
A-dF(v)+F*div(v)=6F*E/Z^2+F^2*Qstar.
```

An independent audit substitutes a concrete current depending rationally on every base coordinate and p, then literally differentiates all five ambient vector components. A separate nonzero auxiliary source with `E=0` checks the conditional zero-obstruction case; that auxiliary source is explicitly not the target `A=y^3`.

For the general proof, take `T=e*partial_e+b*partial_b` and `D=e*partial_e-b*partial_b`. Then `D(p)=0`, `D(R)=6Z`, `D(Z)=6R` and `T(p)=2p`. Thus D annihilates all base/p coefficient dependence, including arbitrary p derivatives in `q(H)`, `q(C)` and s. The vertical divergence is `-6s_p+18s/p-K*R/Z^2`. Combining this with `Z^2-f=F*(R-L)` gives the stated complete formula.

This is extraction infrastructure, not a target certificate. The native target prefix has `E != 0`. For a future closed target current, clearing/homogenizing the rational field and proving the denominator is complex-coprime to F remain required.

## Still open

A finite current must serve the complete physical residual, including all endpoint directions, derivatives of weights, branch/deck and normal corrections, and the full boundary/corner gluing. It must then be transported to the original six variables and checked against `F^2*Q` with a legal homogeneous denominator. A scalar primitive, an unweighted trace, or a CM projector does not provide that closure.

No certificate, Lean proof, local kernel verification, protected CI acceptance or solve PR is included. Root and independent-agent literal checks establish the displayed partial identities, not the missing global primitive.

Credit: `fqlx`'s original reduction and packets; `benediamond`'s contact obstruction and endpoint connection; `deanodotdotdot`'s later scoped component and coordinate/character work; the repository certificate/transport framework. This supplement was prepared for `fqlx` with OpenAI Codex algebra, geometry and verification agents. Human review of every AI-generated calculation is not implied.
