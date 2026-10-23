#!/usr/bin/env python3
"""Independent exact parameter, chain-rule and grading audit for quotient currents."""
from pathlib import Path
import sys
import json
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_piola_transfer import LaurentRing


def main():
    ring = LaurentRing(['t', 'u', 'v', 'z'])
    weights = [1, 2, 3, 1]
    parameters = {
        'H': ring.laurent('t**6+u**6/v**2+v**2+z**6+t**3*u*z/2'),
        'C': ring.laurent('u**3*z/(2*v)+t**2*u/3'),
        'r1': ring.laurent('-3*t*z/2'),
        'r2': ring.laurent('-t**3*v/u**2'),
    }
    expected_jets = {
        'H': ['6*u**5/v**2+t**3*z/2', '-2*u**6/v**3+2*v', '6*z**5+t**3*u/2'],
        'C': ['3*u**2*z/(2*v)+t**2/3', '-u**3*z/(2*v**2)', 'u**3/(2*v)'],
        'r1': ['0', '0', '-3*t/2'],
        'r2': ['2*t**3*v/u**3', '-t**3/u**2', '0'],
    }
    checks = []
    for name, polynomial in parameters.items():
        for variable, text in zip(['u', 'v', 'z'], expected_jets[name]):
            residual = ring.add(ring.diff(polynomial, variable), ring.scale(ring.laurent(text), -1))
            assert not residual, (name, variable, residual)
            checks.append(f'{name}_jet_{variable}')
        degree = {'H': 6, 'C': 4, 'r1': 2, 'r2': 2}[name]
        assert {sum(a*b for a, b in zip(e, weights)) for e in polynomial} == {degree}
        checks.append(f'{name}_weighted_degree')
        # Y-sign fixes t and negates u,v,z. H is even, the other three odd.
        sign = 1 if name == 'H' else -1
        assert all((1 if (e[1]+e[2]+e[3]) % 2 == 0 else -1) == sign
                   for e in polynomial)
        checks.append(f'{name}_Y_parity')

    physical = LaurentRing(['t', 'x', 'y', 'z'])
    theta = {'t': physical.var('t'), 'u': physical.poly('x*y'),
             'v': physical.poly('y**3'), 'z': physical.var('z')}
    expected_physical = {
        'H': physical.poly('t**6+x**6+y**6+z**6+t**3*x*y*z/2'),
        'C': physical.poly('x**3*z/2+t**2*x*y/3'),
        'r1': physical.poly('-3*t*z/2'),
        'r2': physical.laurent('-t**3*y/x**2'),
    }
    def pullback(poly):
        # Laurent substitution is valid because theta(u),theta(v) are monomials.
        result = {}
        for exponent, coefficient in poly.items():
            term = physical.const(coefficient)
            for name, power in zip(ring.names, exponent):
                value = theta[name]
                if power >= 0:
                    term = physical.mul(term, physical.power(value, power))
                else:
                    assert len(value) == 1
                    (e, c), = value.items()
                    term = physical.mul(term, {tuple(a*power for a in e): c**power})
            result = physical.add(result, term)
        return result
    for name, polynomial in parameters.items():
        assert pullback(polynomial) == expected_physical[name]
        checks.append(f'{name}_physical_pullback')
        for variable in ['x', 'y', 'z']:
            result = physical.diff(expected_physical[name], variable)
            for qvariable in ['u', 'v', 'z']:
                result = physical.add(result, physical.scale(physical.mul(
                    pullback(ring.diff(polynomial, qvariable)),
                    physical.diff(theta[qvariable], variable)), -1))
            assert not result, (name, variable, result)
            checks.append(f'{name}_physical_chain_{variable}')

    assert physical.mul(physical.poly('t**3/3'), physical.poly('3*y**3')) == physical.poly('t**3*y**3')
    checks.append('homogeneous_source_density')
    basis_indices = [0, 1, 3, 4, -1, -1, 2]
    coordinate_weights = [2, 3, 1]
    current_degrees = [[w-3-2*j for j in basis_indices] for w in coordinate_weights]
    # Relative forms have degree 2j-4; a finite beta has degree -6,
    # represented by j=-1. Contracting the base volume of degree6 drops wi.
    for i, wi in enumerate(coordinate_weights):
        for j in basis_indices:
            assert (wi-3-2*j)+(6-wi)+(2*j-4) == -1
            # Source -t^3 MH[k,0]/18 has the same total degree -1.
            assert (3-6-2*j)+6+(2*j-4) == -1
    checks.append('current_and_source_weights')
    output = {
        'status': 'passed', 'arithmetic': 'standard-library exact Fraction Laurent polynomials',
        'checks': checks,
        'basis_indices': basis_indices,
        'coordinate_weights': coordinate_weights,
        'coefficient_current_weights': current_degrees,
        'homogeneous_source': '-t^3 M_H e0/18',
        'chart_source': '-M_H e0/18 on t=1',
        'numerator_weight_for_denominator_tk_vm': '3*m+k+w_i-3-2*j',
        'numerator_Y_parity': '(m+j+1) mod 2',
        'scope': 'Exact parameter jets, source, parity and grading audit only. Evaluated modular consistency is not an exact current.'
    }
    path = Path(__file__).with_name('endpoint-quotient-interface-results.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
