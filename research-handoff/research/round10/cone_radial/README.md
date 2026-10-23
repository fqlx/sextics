# Finite cone-amplitude current test

The frame uses the exact canceled canonical pencil normalization from
`round9/abel_prym/effective_physical.pickle`: N0p=den, N1p=num. It is distinct
from physical old-coordinate graph numerator/denominator and no units are
silently changed. `frame.py` and `frame.pickle` supply the dual fields for
(N0p,N1p,v), the Euler field E, radial field E/N0p², and pencil-s direction.
All values and gradients satisfy the dual/Euler identities. The independent
audit is `/workspace/research/round9/marked_log_module/radial_audit.json`.

`search.py` evaluates these fields against the fully audited horizontal
rank-five source system. It retains the cubic-root density, the complete
physical derivative of s=N1p/N0p, and every scalar/current divergence. It
checks Piola's identity `div(radial)=-radial(log Jab)` at every point.
The optional cone density Jab/fT gives the leading two holomorphic current
modes radial*(1,s) in the sigma0 component without dropping rho derivatives.

Two modest modules were tested modulo1000003. The first uses radial,
pencil-s, and v directions, all five Prym components, three densities
rho/rho*fT/cone, and (1,s):90columns, ranks90/91. The second additionally
uses N0p powers -1,0,1 and subtracts the known first current:270columns,
ranks270/271. Arguments, labels, and sample points are in the JSON/pickle
outputs. Neither produced a candidate. No unrestricted exclusion follows.

The contracted cone's local nonrationality is not itself a global H20
statement for the physical degree32 support, which already retains the
genus-four exceptional surface. The independent global twist/adjoint jet
calculation is in `../horizontal5/global_twists/README.md`; boundary
normalization/conductor conditions remain open. No certificate is asserted.
