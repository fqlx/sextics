#!/usr/bin/env python3
"""Independent exact Poisson/source-potential and Hamiltonian-frame audit."""
from pathlib import Path
from fractions import Fraction as Q
import sys
import json
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)
    coeff = Ring(['p', 'H', 'B', 'C'])
    g = coeff.poly('3*C*p**2+B')
    p = coeff.var('p')
    # D_B p=-p/g and D_B g=(B-3Cp^2)/g. Clear g^3.
    second_num = coeff.add(coeff.mul(p, g), coeff.mul(p, coeff.poly('B-3*C*p**2')))
    check('p_BB_equals_twice_source', coeff.add(second_num, coeff.poly('-2*B*p')))
    check('F_B_derivative_equals_actual_source', coeff.add(coeff.scale(second_num, Q(1, 2)), coeff.poly('-B*p')))

    # Total coefficient gradients of p and p_B have denominators g and g^3.
    dp = [coeff.const(-1), coeff.poly('-p'), coeff.poly('-p**3')]
    dpB = [coeff.poly('B-3*C*p**2'), coeff.poly('2*B*p'), coeff.poly('4*B*p**3+6*C*p**5')]
    for i, j, target in [(0, 1, '-p'), (0, 2, '-3*p**3'), (1, 2, '-2*p**4')]:
        numerator = coeff.add(coeff.mul(dp[i], dpB[j]), coeff.scale(coeff.mul(dp[j], dpB[i]), -1))
        check('extended_p_pB_wedge_'+str(i)+str(j), coeff.add(numerator,
                  coeff.scale(coeff.mul(coeff.poly(target), g), -1)))

    r = LaurentRing(['z', 'U', 'K', 't'])
    rho = r.laurent('1/(18*t*z**2)')
    check('symplectic_volume_exact_density', r.add(r.mul(r.laurent('1/(3*z**2)'), r.laurent('1/(6*t)')),
                                                  r.scale(rho, -1)))
    zero = {}
    # X_F^i=sum_j A[i,j] D_j(F), with i_XF omega=-dF.
    A = [[zero.copy() for _ in range(4)] for _ in range(4)]
    A[0][1], A[1][0] = r.poly('-3*z**2'), r.poly('3*z**2')
    A[2][3], A[3][2] = r.poly('-6*t'), r.poly('6*t')
    logs = [r.laurent('-2/z'), {}, {}, r.laurent('-1/t')]
    for j in range(4):
        # Coefficients of the independent first derivatives of arbitrary F.
        check('Hamiltonian_divergence_first_derivative_'+str(j), r.add(*(
            r.add(r.diff(A[i][j], r.names[i]), r.mul(logs[i], A[i][j])) for i in range(4))))
    for i in range(4):
        for j in range(i+1, 4):
            # Mixed derivatives commute also in the finite separable field.
            check('Hamiltonian_divergence_mixed_derivative_'+str(i)+str(j), r.add(A[i][j], A[j][i]))
    def bracket(F, G):
        result = {}
        for i in range(4):
            for j in range(4):
                result = r.add(result, r.mul(A[i][j], r.mul(r.diff(F, r.names[j]), r.diff(G, r.names[i]))))
        return result
    frame = [[{}, r.poly('3*z**2'), {}, {}],
             [r.poly('-3*z**2'), {}, {}, {}],
             [{}, {}, {}, r.poly('6*t')],
             [{}, {}, r.poly('-6*t'), {}]]
    for h in range(4):
        for i in range(4):
            check('coordinate_Hamiltonian_frame_'+str(h)+str(i),
                  r.add(A[i][h], r.scale(frame[h][i], -1)))
    H = r.poly('1+z**2+t')
    B = r.poly('U/2+K/3+z*U*K/2')
    C = r.laurent('1/z**2+U**6+K**6/t')
    check('physical_H_C_bracket', r.add(bracket(H, C), r.poly('-36*z**3*U**5+36*K**5')))
    # The coordinate Hamiltonian matrix is invertible on z*t!=0, so it
    # represents every L-valued base current, not merely a new subspace.
    inverse = [[{}, r.laurent('1/(3*z**2)'), {}, {}],
               [r.laurent('-1/(3*z**2)'), {}, {}, {}],
               [{}, {}, {}, r.laurent('1/(6*t)')],
               [{}, {}, r.laurent('-1/(6*t)'), {}]]
    # inverse[h,i] converts the ordinary current component a_i to the
    # coefficient multiplying X_(q_h).
    for i in range(4):
        for j in range(4):
            residual = r.add(*(r.mul(A[i][h], inverse[h][j]) for h in range(4)),
                             r.const(-1 if i == j else 0))
            check('complete_Hamiltonian_frame_inverse_'+str(i)+str(j), residual)
    result = {'status': 'passed', 'arithmetic': 'standard-library Fraction polynomial and Laurent-polynomial dictionaries',
        'checks': checks, 'count': len(checks),
        'convention': 'X_F(G)={F,G}; i_XF omega=-dF',
        'complete_equation': '{z,b_z}+{U,b_U}+{K,b_K}+{t,b_t}=B*p/g^3',
        'field_extension': 'Every D_i extends uniquely to the separable cubic field and these extensions commute; the Hamiltonian divergence calculation therefore holds for F in L.',
        'scope': 'Complete rational-current representation and exact source-potential identities only. Trace zero or a Darboux pair alone does not prove bracket exactness.'}
    out = Path(__file__).with_name('poisson-fraction-results.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
