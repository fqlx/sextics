# A centered mixed logarithmic current for the cycle-q2 residual

Prepared for fqlx with OpenAI ChatGPT assistance. The candidate reduction was obtained using ChatGPT in Chrome and checked independently with the included exact SymPy scripts. No rational primitive, Lean theorem for this packet, or protected certificate is claimed.

## Scope and reproduction

Use Python 3 with SymPy 1.14.0. Run `python replay.py` and `python centered.py` in this directory. The second run took about one minute on the development host. All arithmetic is rational and symbolic. The JSON receipts record successful checks and the unsolved equation.

These scripts start with the cubic H and quartic P printed in `receipt.json`, and the already transported residual coefficient G printed in `centered.py`. They check that G is `-I^2/12 D_I(p/K) D_J^2(T/b^4)`, with K=H_p and Q=P_T and with all implicit derivatives retained. They do not independently reprove the earlier transport from the original sextic instance to this residual.

## Exact divergence formula

Put f=b-y^2, N=y^3 p^2/K,

    theta_I = -P_I/(2 b^2 T Q),
    theta_J = b^7/(2 Q),
    theta_I_centered = theta_I + 3/(4 I b^2),
    O_centered = D_J(N) theta_I_centered - D_I(N) theta_J,
    V = D_y + 2 y D_b.

For every rational U in the full mixed function field, the four coefficients

    A_y = U/f,
    A_b = 2 y U/f,
    A_I = -N theta_J/f,
    A_J = N theta_I_centered/f

satisfy the literal identity

    D_y A_y + D_b A_b + D_I A_I + D_J A_J
        = (V(U) + O_centered)/f.

The check retains U as an arbitrary function of all six displayed symbols and uses the actual implicit p and T derivatives. Thus a rational solution of `V(U)=f G-O_centered` would yield a primitive for this residual through these four coefficients. No such U has been found.

## Why the centering matters

The uncorrected quartic parameter coefficients have traces

    Tr_D(theta_I) = -3/(I b^2),  Tr_D(theta_J)=0.

These follow from Lagrange's trace identity `Tr(A(T)/P_T)=coeff(T^3,A)/I^6` for degree(A)<4. The correction makes both traces zero. Likewise `Tr_C(N)=y^3/(1+y^6)`, independent of I,J, so the parameter derivatives of N have zero cubic trace. Both O_centered and G lie in the tensor product of the two-dimensional cubic trace kernel and the three-dimensional quartic trace kernel.

For comparison, the uncorrected equation forces its normalized quartic trace S to satisfy

    D_y S = r/(y^2+f)^2,
    r = -3 y^4 p(p+I)/(4 I K^3),

with f held constant. At I=1,J=2,f=-1,y=1,p=-1 one has H=0 and K=11/2. The residue of this right side times dy is

    D_y(r)/(4 y^2) - r/(4 y^3) = 18/14641.

The source residue is a rational function on the generic finite boundary locus and has a defined nonzero specialization. It is therefore not identically zero. A rational derivative on a smooth normalized curve has zero residues, so this uncorrected logarithmic ansatz cannot solve its equation, even with arbitrary rational U. This excludes that ansatz only. It does not exclude independently adjustable horizontal residues, higher f-poles, other divisors, or general four-component currents.

## The remaining six-dimensional equation

An explicit centered cubic basis is

    u1 = p + y/(6(1+y^6)),
    u2 = p^2 - y^2/(12(1+y^6)^2) + I y/(3(1+y^6)).

An explicit centered quartic basis is

    v1 = T,
    v2 = T^2 + b^9/(2 I^6),
    v3 = T^3 + 3(I b^8/2-J b^9)/(4 I^6).

Newton identities, checked by the actual companion matrices, give zero trace for all five basis elements. Normalized trace projections commute with V. Consequently any solution of the corrected equation projects to one in the six-dimensional tensor product. On setting b=y^2+f, write U as the sum of c_ij(I,J,y,f) u_i v_j. The coefficients satisfy a first-order rational system in y, with connection `M_C tensor 1 + 2y 1 tensor M_D`; M_C and M_D come from reducing the actual derivatives of these basis elements modulo H and P.

The system has not been constructed or solved in this packet. In particular, removing the scalar trace obstruction is not a proof of rational solvability or of the original protected theorem.
