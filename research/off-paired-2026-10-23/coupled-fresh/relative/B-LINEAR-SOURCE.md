# Birational coefficient chart with its actual density

No primitive or certificate is supplied here. This calculation preserves the
complete source; it supplies a coordinate option for constructive work.

On the full G36 chart, retain z,U and replace K,t by B,C. Put

    L=2+3zU,
    K=(6B-3U)/L,
    Q=C-z^(-2)-U^6,
    t=K^6/Q,
    H=1+z^2+K^6/Q.

This is birational on LQKzt≠0. In the displayed order,

    Ω=− dz∧dU∧dB∧dC/(3z^2 LQ).

In particular its density is independent of B. Its logarithmic derivative is

    ell_z=−2/z−3U/L−2/(z^3Q),
    ell_U=−3z/L+6U^5/Q,
    ell_B=0,
    ell_C=−1/Q.

The complete two-current connection remains unchanged in form when ordinary
divergence is replaced by divergence for this displayed density. Here
κ=B³/(CH²), so in particular

    ∂B logκ=3/B−2 H_B/H,   H_B=36K^5/(LQ),
    ∂C logκ=−1/C−2 H_C/H, H_C=−K^6/Q².

These derivatives are nonzero; this coordinate change does not make κ an
independent physical coordinate.

## A source-carrying current with the exact remaining term

Let q=p_B=−p/(B+3Cp²), where the subscript means universal coefficient
differentiation at fixed H,C. In the actual cubic field,

    q_B=2R,
    q_H=−q/(3H)−4BR/(3H),
    q_C=−2q/(3C)−2BR/(3C).

The physical coordinate derivative ∂B at fixed z,U,C therefore gives

    divΩ(q ∂B/2)=R+(H_B/2) q_H.

Equivalently the remaining actual source after this current is

    −(H_B/2)q_H=H_B(q+4BR)/(6H).

The derivative of H must be retained. The density independence of B alone
therefore does not produce the primitive.

The fixed-H coefficient lift

    V=∂B+v∂C,   v=36Q/(LK),

has divΩ(V)=0 and V(H)=0, but

    divΩ(qV)=(2−2Bv/(3C))R−2vq/(3C).

This vector is precisely the original K-direction after coordinate change;
it does not give an additional volume-preserving coefficient flow.

`b_linear_coordinates.py` verifies nine exact coordinate/source identities
with SymPy. No denominator-family search was performed and no unrestricted
nonexistence conclusion is asserted.
