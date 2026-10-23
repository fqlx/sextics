#!/usr/bin/env python3
"""Independent Fraction checks of first quartic currents and normal-source cycle."""
from pathlib import Path
import sys
import json
from fractions import Fraction as Q
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_piola_transfer import LaurentRing


def main():
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)
    p = Ring(['u', 'v', 'z', 'a', 'b'])
    S = p.poly('1+z**6+a**6+b**6+u*z/2+u*a*b/3')
    T = p.poly('u**3*z*a*b/2')
    R = p.poly('u**6')
    G = p.add(p.poly('v**4'), p.mul(S, p.poly('v**2')), p.mul(T, p.var('v')), R)
    D = p.poly('a**6-b**6')
    K0 = p.add(p.scale(S, Q(1, 3)),
               p.poly('u*z/36-u*a*b/27'))
    # M=D*N, so all directional and divergence computations are polynomial.
    M = [p.scale(p.mul(p.var('u'), D), Q(-1, 18)),
         p.scale(p.mul(p.var('v'), D), Q(-1, 3)), {},
         p.scale(p.mul(p.var('a'), p.add(K0, p.scale(p.poly('b**6'), -1))), Q(1, 6)),
         p.scale(p.mul(p.var('b'), p.add(p.poly('a**6'), p.scale(K0, -1))), Q(1, 6))]
    def directional(poly):
        result = {}
        for m, variable in zip(M, p.names):
            result = p.add(result, p.mul(m, p.diff(poly, variable)))
        return result
    for name, poly, constant in [('S', S, Q(1, 3)), ('T', T, Q(0)), ('R', R, Q(-1, 3))]:
        check('first_direction_'+name, p.add(directional(poly), p.scale(p.mul(D, poly), -constant)))
    check('first_direction_G', p.add(directional(G), p.scale(p.mul(D, G), Q(1, 3)), p.mul(D, p.poly('v**4'))))
    divM = p.add(*(p.diff(m, variable) for m, variable in zip(M, p.names)))
    div_num = p.add(p.mul(D, divM), p.scale(directional(D), -1))
    h_num = p.add(p.scale(p.power(D, 2), Q(4, 9)),
                  p.scale(p.mul(p.poly('a**6+b**6'), K0), -1), p.poly('2*a**6*b**6'))
    check('first_divergence', p.add(div_num, p.scale(p.power(D, 2), Q(1, 3)), p.scale(h_num, -1)))
    check('first_source_and_correction', p.add(p.mul(G, div_num),
          p.scale(p.mul(D, directional(G)), -1),
          p.scale(p.mul(p.poly('v**4'), p.power(D, 2)), -1),
          p.scale(p.mul(G, h_num), -1)))
    # Divide the displayed N by 3 to bind the actual source v^4/(3G^2).
    check('first_actual_source_factor', p.add(p.scale(p.mul(G, div_num), Q(1, 3)),
          p.scale(p.mul(D, directional(G)), Q(-1, 3)),
          p.scale(p.mul(p.poly('v**4/3'), p.power(D, 2)), -1),
          p.scale(p.mul(G, h_num), Q(-1, 3))))
    Kbase = p.poly('(1+z**6)/3+7*u*z/36')
    check('first_Kbase_binding', p.add(K0, p.scale(p.add(p.poly('(a**6+b**6)/3+2*u*a*b/27'), Kbase), -1)))

    endpoint = Ring(['p', 'H', 'C', 'u', 'Kb'])
    f = endpoint.poly('(H+C*p)**2-4*p**6')
    Kp = endpoint.poly('-(H+C*p)/3+Kb+2*u*p/27')
    numerator = endpoint.add(endpoint.scale(f, Q(4, 9)),
                  endpoint.mul(endpoint.poly('H+C*p'), Kp), endpoint.poly('2*p**6'))
    exact = endpoint.scale(endpoint.add(f, endpoint.scale(endpoint.mul(endpoint.var('p'), endpoint.diff(f, 'p')), Q(-1, 2))), Q(1, 36))
    rest = endpoint.poly('(H+C*p)*(H/12+Kb+(C/9+2*u/27)*p)')
    check('first_endpoint_Hermite', endpoint.add(numerator, endpoint.scale(exact, -1), endpoint.scale(rest, -1)))

    base = LaurentRing(['u', 'v', 'z'])
    H = base.laurent('1+u**6/v**2+v**2+z**6+u*z/2')
    C = base.laurent('u**3*z/(2*v)+u/3')
    Kb = base.poly('(1+z**6)/3+7*u*z/36')
    W = [base.laurent('-u/(18*v**2)'), base.laurent('-1/(3*v)'), {}]
    divW = base.add(*(base.diff(w, variable) for w, variable in zip(W, base.names)))
    def apply(poly):
        return base.add(*(base.mul(w, base.diff(poly, variable)) for w, variable in zip(W, base.names)))
    check('cycle_divergence', base.add(divW, base.laurent('-5/(18*v**2)')))
    RH = base.scale(base.mul(base.add(base.scale(H, Q(1, 12)), Kb), base.laurent('1/v**2')), -1)
    RC = base.scale(base.mul(base.add(base.scale(C, Q(1, 9)), base.poly('2*u/27')), base.laurent('1/v**2')), -1)
    check('cycle_H_coefficient_one', base.add(apply(H), base.scale(base.mul(H, divW), Q(-3, 2)),
          base.scale(RH, -1), base.const(1)))
    check('cycle_C_coefficient', base.add(apply(C), base.scale(base.mul(C, divW), -1), base.scale(RC, -1)))

    normal = LaurentRing(['Y', 'G', 'v'])
    B = normal.laurent('-2*v**4/(3*Y)')
    Bt = normal.laurent('-2*v**4*Y/(3*G)')
    def normal2(poly):
        return normal.add(normal.mul(normal.diff(poly, 'Y'), normal.laurent('1/(4*Y**2)')),
                          normal.scale(normal.mul(poly, normal.laurent('1/(4*Y**3)')), -1))
    check('companion_actual_second_normal', normal.add(normal2(B), normal.laurent('-v**4/(3*Y**4)')))
    check('companion_polynomialized_second_normal_zero', normal2(Bt))
    check('companion_boundary_not_dropped', normal.add(B, normal.scale(Bt, -1),
          normal.scale(normal.mul(normal.laurent('2*v**4/(3*Y*G)'), normal.poly('Y**2-G')), -1)))
    first = normal.laurent('v**4/(3*Y**2*G)')
    # first - v^4/(3G^2) = -v^4 (Y^2-G)/(3Y^2G^2).
    check('companion_first_normal_returns_original', normal.add(first, normal.laurent('-v**4/(3*G**2)'),
          normal.mul(normal.laurent('v**4/(3*Y**2*G**2)'), normal.poly('Y**2-G'))))
    result = {'status': 'passed', 'arithmetic': 'standard-library Fraction polynomials and Laurent polynomials',
              'checks': checks,
              'first_current_scaling': 'Displayed N solves source v^4. Divide N by 3 for actual source v^4/3; correction is h/(3G).',
              'cycle_coefficient': 1,
              'orientation': 'Companion normal operator assumes dY ordered before the five base differentials. Quartic scalar residue r corresponds to -r du∧dz∧da∧db when dG is placed first in du∧dv∧dz∧da∧db.',
              'scope': 'Exact identities and failure of the proposed self-closure. No primitive or certificate.'}
    out = Path(__file__).with_name('first-current-fraction-results.json')
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
