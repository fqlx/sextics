#!/usr/bin/env python3
"""Independent algebraic checks for the conditional endpoint-current lift."""
from pathlib import Path
from fractions import Fraction as Q
import sys
import json
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_piola_transfer import LaurentRing


def main():
    r = LaurentRing(['u', 'v', 'z', 'a', 'b', 'h0', 'h1', 'h2', 'A0', 'P'])
    H = r.laurent('1+u**6/v**2+v**2+z**6+u*z/2')
    C = r.laurent('u**3*z/(2*v)+u/3')
    F = r.add(r.poly('a**6+b**6'), r.mul(C, r.poly('a*b')), H)
    Z = r.poly('b**6-a**6')
    T = r.var('A0')
    h = [r.var('h0'), r.var('h1'), r.var('h2')]
    Li = [r.diff(F, q) for q in ['u', 'v', 'z']]
    for hi, li in zip(h, Li):
        T = r.add(T, r.scale(r.mul(hi, li), 6))
    Fa, Fb = r.diff(F, 'a'), r.diff(F, 'b')
    Va_num = r.add(r.mul(Fb, r.var('P')), r.scale(r.mul(r.var('a'), T), -1))
    Vb_num = r.add(r.mul(r.var('b'), T), r.scale(r.mul(Fa, r.var('P')), -1))
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)
    residual = r.add(r.mul(Fa, Va_num), r.mul(Fb, Vb_num),
                     r.scale(r.mul(Z, r.var('A0')), -6))
    for hi, li in zip(h, Li):
        residual = r.add(residual, r.scale(r.mul(Z, r.mul(hi, li)), -36))
    check('lift_exact_normal_VF_equals_A0', residual)
    check('lift_exact_Vp_equals_P', r.add(r.mul(r.var('b'), Va_num),
              r.mul(r.var('a'), Vb_num), r.scale(r.mul(Z, r.var('P')), -6)))

    # Abstract coefficient identity at F=0. The formal variables Li mean
    # H_i+C_i p, and di mean partial_i h_i at fixed p.
    a = LaurentRing(['f', 'fp', 'S', 'A0', 'P', 'Pp',
                     'h0', 'h1', 'h2', 'd0', 'd1', 'd2', 'L0', 'L1', 'L2'])
    total_hL = a.add(*(a.mul(a.var('h'+str(i)), a.var('L'+str(i))) for i in range(3)))
    total_d = a.add(*(a.var('d'+str(i)) for i in range(3)))
    T = a.add(a.var('A0'), a.scale(total_hL, 6))
    div_times_f = a.add(a.scale(a.mul(a.var('f'), total_d), -6),
        a.mul(a.var('f'), a.var('Pp')), a.mul(T, a.var('S')),
        a.scale(a.mul(a.var('P'), a.var('fp')), Q(-1, 2)))
    # beta_1=-A0/6 partial_H(dp/Z)=+A0*S dp/(6Z^3).
    # Thus d_eta-beta_1 has the negative source term below. The normal
    # divergence is -6Z times this literal one-form coefficient.
    literal_difference = a.add(a.scale(a.mul(a.var('f'), total_d), 6),
        a.scale(a.mul(a.var('S'), total_hL), -6),
        a.scale(a.mul(a.var('f'), a.var('Pp')), -1),
        a.scale(a.mul(a.var('P'), a.var('fp')), Q(1, 2)),
        a.scale(a.mul(a.var('A0'), a.var('S')), -1))
    check('lift_divergence_from_literal_residue', a.add(div_times_f, literal_difference))
    result = {'status': 'passed', 'checks': checks,
        'scope': 'Conditional field assembly checks only. Source-sign and exact Dwork terms must follow CURRENT-TO-WITNESS.md.'}
    path = Path(__file__).with_name('current-lift-fraction-results.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
