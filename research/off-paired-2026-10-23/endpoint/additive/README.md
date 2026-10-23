# Coupled simple-pole current attempt

This is a focused constructive search for the exact original source in the
chart `X0=1`, with `x=X1,y=Y0,z=Y1` and `Z=Y2^6-X2^6`. The current basis is
`omega_j=p^j dp/Z`, `j=0,1,2,3,4`. The `j=2` component has constant opposite
residues at the two endpoint infinities and its divergence is constrained.

The compact current is the additive sum

```
a_i = P_i/H + Q_i/(2 C^3+27 H^2) + R_i/(2 C^3-27 H^2).
```

The numerator degrees and coordinate characters are the original homogeneous
ones, without an affine degree extension. All three pole families are solved
together, allowing cancellation between their covariant divergences. The
source is `-y^3 M_H e0/6`. The five output rows include the infinity residue row.

`merged_simple_poles.py` produced an inconsistent sampled system modulo 1009:
2740 unknowns, 1434 generic points, 7170 rows, rank 2675. Because the sampled
system was inconsistent, no escalation to the full point count was needed.
This is restricted modular search feedback, not a proof of rational
nonexistence or a solution to the original instance.

`merged_log_residue.py` adds three actual source-carrying classes from the
physical finite pole `s=-3z/2`. Put `L=H+sC`, `T^2=L^2-4s^6`,
`r=(L+T)/(2s^3)`, and `lambda=dL-3L dz/z`. For `g=x,y,z`, the vector
`V=lambda cross dlog(g)` gives the rational current `V beta_s`, where
`beta_s=dp/((p-s)Z)`. Its endpoint divergence is

```
div_nabla(V beta_s) = K_g M_H e0
                    - (V(s)/s) d_p[p/((p-s)Z)],
K_g = V(C)-2 C V(s)/s.
```

The displayed vertical exact correction is included through its known
source column. This follows from the exact conic identity
`T dlog(r)=lambda`; these residue classes need not be rational exact curl
potentials. The augmented system was also inconsistent modulo 1009:
2743 unknowns, 1436 generic points, 7180 rows, rank 2678. No certificate or
candidate was produced.

The generic-point rules deliberately distinguish inconsistency from
consistency. Any inconsistent subset rejects that sampled modular ansatz.
Consistency would require at least one generic point per unknown, then 600
fresh points, rational reconstruction, and an exact full polynomial identity
before any mathematical claim. Neither run reached consistency.

`block_modular.py` uses exact bounded-integer float64 panel products and
reduces after each update. It asserts canonical integral inputs, the
`panel_size*(p-1)^2 < 2^53` float bound, and the
`n*(p-1)^2 < 2^63` int64 bound for back substitution and final verification.
The independent verifier audited its pivot/update logic and passed 396
comparisons on 99 known-rank systems, including a panel close to the
float64 exact-integer bound. Audit files are in `../../audit/`.

Results are retained in `merged-simple-poles-results.json` and
`merged-log-residue-results.json`. They do not close the open compact
correction or the physical source problem.
