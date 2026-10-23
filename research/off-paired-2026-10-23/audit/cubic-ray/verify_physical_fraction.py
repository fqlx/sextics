#!/usr/bin/env python3
"""Independent source, Piola and Nambu audits of both cubic-ray interfaces."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import sys
import json
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def determinant(matrix):
    n = len(matrix)
    result = Q(0)
    for perm in permutations(range(n)):
        sign = -1 if sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n)) % 2 else 1
        term = Q(sign)
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        result += term
    return result


def monomial_pullback(ring, polynomial, target, values):
    result = {}
    for exponent, coefficient in polynomial.items():
        term = target.const(coefficient)
        for name, power in zip(ring.names, exponent):
            value = values[name]
            assert len(value) == 1
            (e, c), = value.items()
            term = target.mul(term, {tuple(a*power for a in e): c**power})
        result = target.add(result, term)
    return result


def main():
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)
    phys = LaurentRing(['x', 'a', 'y', 'Y1', 'Y2'])
    F = phys.poly('1+x**6+a**6+y**6+Y1**6+Y2**6+'
                  'x*y*Y1/2+x**3*a*Y1*Y2/2+x*a*y*Y2/3')
    high = LaurentRing(['x', 'a', 's', 'u', 'v'])
    H = high.poly('1+x**6+a**6')
    B = high.poly('x*u/2+x**3*a*u*v/2+x*a*v/3')
    C = high.poly('1+u**6+v**6')
    f = high.add(H, high.mul(B, high.var('s')), high.mul(C, high.poly('s**3')))
    theta = {q: phys.laurent(text) for q, text in zip(high.names,
                            ['x', 'a', 'y**2', 'Y1/y', 'Y2/y'])}
    pull = lambda poly: monomial_pullback(high, poly, phys, theta)
    check('high_immutable_equation', phys.add(pull(f), phys.scale(F, -1)))
    J = phys.laurent('2/y')
    check('high_actual_density', phys.add(phys.mul(J, pull(high.poly('s**2/2'))), phys.poly('-y**3')))
    exponents = [list(next(iter(theta[q]))) for q in high.names]
    assert determinant(exponents) == 2
    checks.append('high_monomial_Jacobian_exponent_determinant')
    prefactors = [
        ['2/y', '0', '0', '0', '0'],
        ['0', '2/y', '0', '0', '0'],
        ['0', '0', '1/y**2', '0', '0'],
        ['0', '0', 'Y1/y**3', '2', '0'],
        ['0', '0', 'Y2/y**3', '0', '2'],
    ]
    P = [[phys.laurent(t) for t in row] for row in prefactors]
    jac = [[phys.diff(theta[q], p) for p in phys.names] for q in high.names]
    for i in range(5):
        for j in range(5):
            check('high_Piola_first_jet_'+str(i)+str(j), phys.add(*(
                 phys.mul(jac[i][k], P[k][j]) for k in range(5)),
                 phys.scale(J, -1 if i == j else 0)))
    for j in range(5):
        check('high_Piola_zero_order_'+str(j), phys.add(*(
              phys.diff(P[i][j], phys.names[i]) for i in range(5))))
    g = high.diff(f, 's')
    for q in ['x', 'a', 'u', 'v']:
        check('high_normal_jacobian_jet_'+q,
              high.add(high.diff(high.diff(f, q), 's'), high.scale(high.diff(g, q), -1)))
    check('high_actual_normal_R', high.add(high.mul(high.var('s'), g),
          high.scale(high.mul(high.poly('s**2/2'), high.diff(g, 's')), -1),
          high.scale(high.mul(B, high.var('s')), -1)))

    # Low-degree full-G36 quotient. All five coordinate functions are
    # monomials, so both the map degree and its signed Jacobian are exact.
    low = LaurentRing(['z', 'U', 'K', 't', 'p'])
    Hl = low.poly('1+z**2+t')
    Bl = low.poly('U/2+K/3+z*U*K/2')
    Cl = low.laurent('1/z**2+U**6+K**6/t')
    fl = low.add(Hl, low.mul(Bl, low.var('p')), low.mul(Cl, low.poly('p**3')))
    theta_l = {q: phys.laurent(text) for q, text in zip(low.names,
                ['x**3', 'Y1/(x*y)', 'a*Y2/(x*y)', 'a**6', 'x**2*y**2'])}
    pull_l = lambda poly: monomial_pullback(low, poly, phys, theta_l)
    check('low_immutable_equation', phys.add(pull_l(fl), phys.scale(F, -1)))
    exponents_l = [list(next(iter(theta_l[q]))) for q in low.names]
    assert determinant(exponents_l) == 36
    checks.append('low_monomial_map_degree_and_Jacobian_sign')
    product = phys.const(36)
    for q in low.names:
        product = phys.mul(product, theta_l[q])
    product = phys.mul(product, phys.laurent('1/(x*a*y*Y1*Y2)'))
    Jl = phys.laurent('36*a**6*x**2/y')
    check('low_actual_Jacobian', phys.add(product, phys.scale(Jl, -1)))
    A0l = low.laurent('p**2/(36*t*z**2)')
    check('low_actual_density', phys.add(phys.mul(Jl, pull_l(A0l)), phys.poly('-y**3')))
    rho = low.laurent('1/(18*t*z**2)')
    check('low_density_factor_two', low.add(A0l,
          low.scale(low.mul(rho, low.poly('p**2/2')), -1)))
    for q, ell in zip(['z', 'U', 'K', 't'], ['-2/z', '0', '0', '-1/t']):
        check('low_log_density_'+q, low.add(low.diff(rho, q),
              low.scale(low.mul(rho, low.laurent(ell)), -1)))

    # Root's physical lift of W2 and the vertical divergence correction.
    base = Ring(['x', 'a', 'u', 'v'])
    H = base.poly('1+x**6+a**6')
    B = base.poly('x*u/2+x**3*a*u*v/2+x*a*v/3')
    C = base.poly('1+u**6+v**6')
    hx, ha = base.diff(H, 'x'), base.diff(H, 'a')
    bx, ba = base.diff(B, 'x'), base.diff(B, 'a')
    bu, bv = base.diff(B, 'u'), base.diff(B, 'v')
    cu, cv = base.diff(C, 'u'), base.diff(C, 'v')
    JJ = base.add(base.mul(hx, ba), base.scale(base.mul(ha, bx), -1))
    YB = [ba, base.scale(bx, -1), {}, {}]
    YH = [base.scale(ha, -1), hx, {}, {}]
    Nbar = [base.add(base.scale(base.mul(base.power(B, 2), yb), Q(-2, 3)),
                    base.scale(base.mul(base.mul(C, H), yh), 3)) for yb, yh in zip(YB, YH)]
    apply = lambda field, poly: base.add(*(base.mul(w, base.diff(poly, q)) for w, q in zip(field, base.names)))
    check('physical_Mobius_N2_divergence', base.add(*(base.diff(w, q) for w, q in zip(Nbar, base.names))))
    check('physical_Mobius_H_lift', base.add(apply(Nbar, H), base.scale(base.mul(base.power(B, 2), JJ), Q(2, 3))))
    check('physical_Mobius_B_lift', base.add(apply(Nbar, B), base.scale(base.mul(base.mul(C, H), JJ), -3)))
    check('physical_Mobius_C_fixed', apply(Nbar, C))
    GG = base.add(base.mul(bu, cv), base.scale(base.mul(bv, cu), -1))
    K = [base.mul(ha, GG), base.scale(base.mul(hx, GG), -1),
         base.mul(JJ, cv), base.scale(base.mul(JJ, cu), -1)]
    for name, poly in [('H', H), ('B', B), ('C', C)]:
        check('vertical_Nambu_annihilates_'+name, apply(K, poly))
    check('vertical_Nambu_divergence', base.add(*(base.diff(w, q) for w, q in zip(K, base.names))))
    assert JJ and apply(Nbar, JJ), 'the displayed physical defect must be nonzero'
    checks.append('physical_Mobius_divergence_defect_nonzero')
    result = {'status': 'passed', 'arithmetic': 'standard-library Fraction polynomial and Laurent-polynomial dictionaries',
        'checks': checks, 'count': len(checks),
        'high_source': 's^2/(2*f^2) dx da ds du dv',
        'low_source': 'p^2/(36*t*z^2*f^2) dz dU dK dt dp',
        'normal_orientation': 'df first; ds crosses two preceding X differentials, and dp crosses four preceding quotient differentials, both positive',
        'low_log_density': ['-2/z', '0', '0', '-1/t'],
        'Nambu_criterion': 'K(h)=N2(J)/J^2 is the required scalar condition because div(N2)=div(K)=0 and K fixes H,B,C',
        'scope': 'Exact physical source and conditional transport audits. No scalar correction or rank-two current has been constructed.'}
    out = Path(__file__).with_name('physical-fraction-results.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
