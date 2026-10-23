#!/usr/bin/env python3
"""Independent exact finite cubic connection, source and Mobius-flow audit."""
from pathlib import Path
from fractions import Fraction as Q
import sys
import json
import hashlib
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing
from verify_ferrari_fraction import monic_first_variable_remainder


def main():
    r = LaurentRing(['s', 'H', 'B', 'C'])
    endpoint = Path(__file__).resolve().parent.parent.parent/'endpoint/cubic-ray'
    data_path = endpoint/'finite-connection-results.json'
    data = json.loads(data_path.read_text())
    f = r.poly('C*s**3+B*s+H')
    monic = r.laurent('s**3+B*s/C+H/C')
    g = r.diff(f, 's')
    delta = r.poly('4*B**3+27*C*H**2')
    I = r.poly('4*B**2+6*B*C*s**2-9*C*H*s')
    common = r.mul(r.var('C'), delta)
    matrices = {v: [[r.cleared(text, common) for text in row]
                    for row in data['matrices'][v]] for v in ['H', 'B', 'C']}
    sources = [r.cleared(text, r.power(delta, 2)) for text in data['source']]
    checks = []
    def check(name, residual, field=False):
        if field:
            residual = monic_first_variable_remainder(r, residual, monic, 3)
        assert not residual, (name, residual)
        checks.append(name)
    check('inverse_normal_g', r.add(r.mul(g, I), r.scale(delta, -1)), True)
    for v in ['H', 'B', 'C']:
        for j in range(2):
            # Clear C^2 delta. Differentiating the explicit basis coefficient
            # 2B/(3C) is essential to obtaining the trace-zero matrices.
            direct = {}
            if j == 1 and v == 'B':
                direct = r.scale(r.mul(r.var('C'), delta), Q(2, 3))
            if j == 1 and v == 'C':
                direct = r.scale(r.mul(r.var('B'), delta), Q(-2, 3))
            ej_s = r.const(1) if j == 0 else r.poly('2*s')
            residual = r.add(direct, r.scale(r.mul(r.poly('C**2'),
                           r.mul(ej_s, r.mul(r.diff(f, v), I))), -1))
            residual = r.add(residual, r.scale(r.mul(r.poly('C*s'), matrices[v][0][j]), -1),
                r.scale(r.mul(r.poly('C*s**2+2*B/3'), matrices[v][1][j]), -1))
            check('basis_derivative_'+v+'_'+str(j), residual, True)
    for vi, vj in [('H', 'B'), ('H', 'C'), ('B', 'C')]:
        for i in range(2):
            for j in range(2):
                residual = r.add(r.mul(r.diff(matrices[vj][i][j], vi), common),
                    r.scale(r.mul(matrices[vj][i][j], r.diff(common, vi)), -1),
                    r.scale(r.mul(r.diff(matrices[vi][i][j], vj), common), -1),
                    r.mul(matrices[vi][i][j], r.diff(common, vj)))
                for k in range(2):
                    residual = r.add(residual, r.mul(matrices[vi][i][k], matrices[vj][k][j]),
                        r.scale(r.mul(matrices[vj][i][k], matrices[vi][k][j]), -1))
                check('flatness_'+vi+vj+'_'+str(i)+str(j), residual)
    for i in range(2):
        for j in range(2):
            check('coefficient_scaling_'+str(i)+str(j), r.add(*(
                  r.mul(r.var(v), matrices[v][i][j]) for v in ['H', 'B', 'C'])))
            check('root_scaling_'+str(i)+str(j), r.add(
                r.scale(r.mul(r.var('H'), matrices['H'][i][j]), 3),
                r.scale(r.mul(r.var('B'), matrices['B'][i][j]), 2),
                r.scale(common, -(i+1) if i == j else 0)))
    candidate = r.add(r.mul(r.poly('C*s'), sources[0]),
                      r.mul(r.poly('C*s**2+2*B/3'), sources[1]))
    check('actual_source_field', r.add(r.mul(r.poly('C*B*s'), r.power(I, 3)),
              r.scale(r.mul(delta, candidate), -1)), True)
    for i in range(2):
        derivative_square = r.add(r.mul(r.diff(matrices['H'][i][0], 'H'), common),
                         r.scale(r.mul(matrices['H'][i][0], r.diff(common, 'H')), -1))
        for k in range(2):
            derivative_square = r.add(derivative_square,
                           r.mul(matrices['H'][i][k], matrices['H'][k][0]))
        check('source_second_H_derivative_'+str(i), r.add(
              r.mul(r.poly('6*C**3'), sources[i]),
              r.mul(r.var('B'), derivative_square)))

    # Gram numerator C^2 Tr(e_i e_j). The determinant proves nondegeneracy
    # wherever C and delta are nonzero, independently of the chosen basis.
    gram = [[r.poly('-2*B*C'), r.poly('-3*H*C')],
            [r.poly('-3*H*C'), r.poly('2*B**2/3')]]
    for v in ['H', 'B', 'C']:
        for i in range(2):
            for j in range(2):
                residual = r.mul(r.var('C'), r.mul(common, r.diff(gram[i][j], v)))
                if v == 'C':
                    residual = r.add(residual, r.scale(r.mul(common, gram[i][j]), -2))
                for k in range(2):
                    residual = r.add(residual,
                        r.scale(r.mul(r.var('C'), r.mul(matrices[v][k][i], gram[k][j])), -1),
                        r.scale(r.mul(r.var('C'), r.mul(gram[i][k], matrices[v][k][j])), -1))
                check('trace_pairing_'+v+'_'+str(i)+str(j), residual)
    check('trace_pairing_determinant', r.add(r.mul(gram[0][0], gram[1][1]),
          r.scale(r.mul(gram[0][1], gram[1][0]), -1), r.scale(r.mul(r.var('C'), delta), Q(1, 3))))

    # Normal second-pole source includes the derivative of 1/g.
    check('actual_second_normal_source', r.add(r.mul(r.var('s'), g),
          r.scale(r.mul(r.poly('s**2/2'), r.diff(g, 's')), -1), r.poly('-B*s')))

    # Universal coefficient flow W2 and its actual finite-field primitive.
    flowH, flowB = r.laurent('-2*B**2/(3*C)'), r.poly('3*H')
    check('Mobius_preserves_delta', r.add(r.mul(flowH, r.diff(delta, 'H')),
                                        r.mul(flowB, r.diff(delta, 'B'))))
    flow_s_num = r.add(r.scale(flowH, -1), r.scale(r.mul(flowB, r.var('s')), -1))
    flow_g_num = r.add(r.mul(r.poly('6*C*s'), flow_s_num), r.mul(flowB, g))
    check('Mobius_Wg_equals_sg', r.add(flow_g_num,
                  r.scale(r.mul(r.var('s'), r.power(g, 2)), -1)), True)
    check('Mobius_discriminant_identity', r.add(delta,
                  r.scale(r.mul(r.power(g, 2), r.add(g, r.poly('3*B'))), -1)), True)
    F0_numerator = r.poly('3*C*s**2-B')
    flow_F0_num = r.add(r.mul(r.add(flow_g_num, r.scale(r.mul(flowB, g), -2)), g),
                       r.scale(r.mul(F0_numerator, flow_g_num), -3))
    check('Mobius_actual_primitive', r.add(flow_F0_num,
                 r.scale(r.mul(r.poly('B*s'), r.power(g, 2)), -10)), True)
    reduced_F0_num = monic_first_variable_remainder(r,
                       r.mul(F0_numerator, r.power(I, 3)), monic, 3)
    trace_F0_num = {}
    for exponent, c in reduced_F0_num.items():
        power = exponent[0]
        coefficient = {(0,)+exponent[1:]: c}
        if power == 0:
            trace_F0_num = r.add(trace_F0_num, r.scale(coefficient, 3))
        elif power == 2:
            trace_F0_num = r.add(trace_F0_num, r.mul(coefficient, r.laurent('-2*B/C')))
    check('Mobius_F0_trace_zero', trace_F0_num)
    result = {'status': 'passed', 'arithmetic': 'standard-library Fraction polynomials; monic univariate reduction over Q[H,B,C,C^-1]',
        'checks': checks, 'count': len(checks),
        'data_sha256': hashlib.sha256(data_path.read_bytes()).hexdigest(),
        'column_convention': 'derivative_v(e_j)=sum_i Mv[i,j] e_i',
        'basis': data['basis'],
        'source': 'B*s/(3*C*s^2+B)^3',
        'universal_F0_trace_zero': True,
        'scope': 'Exact finite connection/source and universal coefficient-flow primitive; physical volume-preserving lift remains required.'}
    path = Path(__file__).with_name('finite-fraction-results.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
