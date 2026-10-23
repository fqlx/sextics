#!/usr/bin/env python3
"""Exact quotient/source/jet audit for u=xy, v=y^3, G=v^2 F.

Uses only standard-library Fraction arithmetic and the independent audit Ring.
Checks the full first-jet Piola identity, so every rational current W is covered
on the chart where its denominators and y are nonzero. It proves no existence.
"""
from pathlib import Path
import sys
import hashlib
import json
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring


class LaurentRing(Ring):
    def laurent(self, text):
        numerator, denominator = self.rational(text)
        assert len(denominator) == 1, 'only Laurent-polynomial denominators allowed'
        (de, dc), = denominator.items()
        return {tuple(x-y for x, y in zip(e, de)): c/dc
                for e, c in numerator.items()}


def main():
    physical = LaurentRing(['x', 'y', 'z', 'a', 'b'])
    quotient = Ring(['u', 'v', 'z', 'a', 'b'])
    pv, qv = physical.names, quotient.names
    theta = {name: physical.poly(text)
             for name, text in zip(qv, ['x*y', 'y**3', 'z', 'a', 'b'])}
    F = physical.poly('a**6+b**6+(x**3*z/2+x*y/3)*a*b+'
                      '1+x**6+y**6+z**6+x*y*z/2')
    A = physical.poly('y**3')
    G = quotient.poly('u**6+v**4+(1+z**6+a**6+b**6+u*z/2+u*a*b/3)*v**2+'
                      'u**3*z*a*b*v/2')
    B = quotient.poly('v**4/3')
    J = physical.poly('3*y**3')
    S = physical.poly('y**6')
    JS = physical.laurent('3/y**3')
    JS2 = physical.laurent('3/y**9')
    GP = quotient.subst(G, theta, physical)
    BP = quotient.subst(B, theta, physical)
    prefactor_text = [
        ['3/y**4', '-x/y**6', '0', '0', '0'],
        ['0', '1/y**5', '0', '0', '0'],
        ['0', '0', '3/y**3', '0', '0'],
        ['0', '0', '0', '3/y**3', '0'],
        ['0', '0', '0', '0', '3/y**3'],
    ]
    prefactor = [[physical.laurent(text) for text in row]
                 for row in prefactor_text]
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)

    check('scaled_equation_G_pullback', physical.add(GP, physical.scale(physical.mul(S, F), -1)))
    check('physical_source', physical.add(A, physical.scale(physical.mul(JS2, BP), -1)))
    jacobian = [[physical.diff(theta[q], p) for p in pv] for q in qv]
    # This is exactly (J/S) (dtheta)^-1. Check all 25 entries instead of
    # relying on a symbolic inverse or on the generator's Piola formula.
    for j, q in enumerate(qv):
        for i, _ in enumerate(qv):
            result = {}
            for k, _ in enumerate(pv):
                result = physical.add(result, physical.mul(jacobian[j][k], prefactor[k][i]))
            result = physical.add(result, physical.scale(JS, -1 if i == j else 0))
            check(f'first_jet_W{i}_derivative_{q}', result)

    # Coefficients of the five arbitrary values W_i in
    # A-V(F)+F div(V) = J/S^2 [B-W(G)+G div(W)] pulled back.
    # The 25 preceding identities verify all independent first derivatives
    # of W_i. Together these are the entire first-jet polynomial identity.
    for i, q in enumerate(qv):
        result = {}
        for k, p in enumerate(pv):
            result = physical.add(result,
                physical.scale(physical.mul(prefactor[k][i], physical.diff(F, p)), -1),
                physical.mul(F, physical.diff(prefactor[k][i], p)))
        Gq_pullback = quotient.subst(quotient.diff(G, q), theta, physical)
        result = physical.add(result, physical.mul(JS2, Gq_pullback))
        check(f'first_jet_W{i}_value', result)

    # The term -2W_v/v is the derivative of the cleared factor S=v^2.
    # Dropping it from div(V) would fail the W_v coefficient above.
    for i, _ in enumerate(qv):
        result = {}
        for k, p in enumerate(pv):
            result = physical.add(result, physical.diff(prefactor[k][i], p))
        if i == 1:
            result = physical.add(result, physical.laurent('6/y**6'))
        check(f'scaling_divergence_correction_{i}', result)

    # If W=P/E and D=y^6 E(theta), then N=D V has these polynomial
    # coefficients multiplying P(theta), without rational y denominators.
    numerator_text = [
        ['3*y**2', '-x', '0', '0', '0'],
        ['0', 'y', '0', '0', '0'],
        ['0', '0', '3*y**3', '0', '0'],
        ['0', '0', '0', '3*y**3', '0'],
        ['0', '0', '0', '0', '3*y**3'],
    ]
    for i in range(5):
        for j in range(5):
            check(f'cleared_numerator_{i}_{j}', physical.add(
                physical.mul(S, prefactor[i][j]),
                physical.scale(physical.poly(numerator_text[i][j]), -1)))
    check('cleared_remainder_factor', physical.add(
        physical.mul(physical.power(S, 4), JS2),
        physical.scale(physical.poly('3*y**15'), -1)))

    # Bind the homogeneous lift, including the X0^3 factor absent on X0=1.
    qhom = Ring(['t', 'u', 'v', 'z', 'a', 'b'])
    phom = LaurentRing(['t', 'x', 'y', 'z', 'a', 'b'])
    Gh = qhom.poly('u**6+v**4+(t**6+z**6+a**6+b**6+t**3*u*z/2+'
                     't**2*u*a*b/3)*v**2+u**3*z*a*b*v/2')
    Bh = qhom.poly('t**3*v**4/3')
    Fh = phom.poly('t**6+x**6+y**6+z**6+a**6+b**6+'
                    't**3*x*y*z/2+x**3*z*a*b/2+t**2*x*y*a*b/3')
    Ah = phom.poly('t**3*y**3')
    theta_h = {name: phom.poly(text) for name, text in zip(qhom.names,
                            ['t', 'x*y', 'y**3', 'z', 'a', 'b'])}
    check('homogeneous_scaled_equation', phom.add(qhom.subst(Gh, theta_h, phom),
                            phom.scale(phom.mul(phom.poly('y**6'), Fh), -1)))
    check('homogeneous_source_binding', phom.add(Ah,
          phom.scale(phom.mul(phom.laurent('3/y**9'), qhom.subst(Bh, theta_h, phom)), -1)))
    qweights = [1, 2, 3, 1, 1, 1]
    assert {sum(a*b for a, b in zip(e, qweights)) for e in Gh} == {12}
    assert {sum(a*b for a, b in zip(e, qweights)) for e in Bh} == {15}
    assert {sum(e) for e in Fh} == {6}
    assert {sum(e) for e in Ah} == {6}
    current_weights = [5, 6, 4, 4, 4]
    for i in range(5):
        for k in range(5):
            assert all(sum(e)+current_weights[i] == 1 for e in prefactor[k][i])
    checks.append('homogeneous_current_weights')
    target_path = Path('/workspace/off-paired-sextics/data/off-paired/instance.rec')
    target_fields = dict(line.split(': ', 1) for line in target_path.read_text().splitlines()
                         if line.startswith(('F: ', 'A: ', 'q: ')))
    target_ring = Ring(['X0', 'X1', 'X2', 'Y0', 'Y1', 'Y2'])
    target_map = {name: phom.var(replacement) for name, replacement in
                  zip(target_ring.names, ['t', 'x', 'a', 'y', 'z', 'b'])}
    assert target_fields['q'] == '1'
    check('immutable_F_binding', phom.add(Fh, phom.scale(
          target_ring.subst(target_ring.poly(target_fields['F']), target_map, phom), -1)))
    check('immutable_A_binding', phom.add(Ah, phom.scale(
          target_ring.subst(target_ring.poly(target_fields['A']), target_map, phom), -1)))
    output = {
        'status': 'passed',
        'arithmetic': 'standard-library Fraction Laurent polynomial dictionaries',
        'checks': checks,
        'identity': 'A - V(F) + F div(V) = (J/S^2)*(B - W(G) + G div(W)) pulled back',
        'coordinates': {'physical': list(pv), 'quotient': list(qv)},
        'theta': ['x*y', 'y**3', 'z', 'a', 'b'],
        'J': '3*y**3', 'S': 'y**6 = v^2 pulled back',
        'prefactor_V_from_W': prefactor_text,
        'prefactor_N_from_P': numerator_text,
        'cleared_denominator': 'D=y^6 E(theta)',
        'cleared_remainder': 'Q_physical=3*y^15 Q_G(theta)',
        'target_raw_sha256': hashlib.sha256(target_path.read_bytes()).hexdigest(),
        'source_B': 'v^4/3', 'homogeneous_source_B': 't^3*v^4/3',
        'homogeneous_G_weight': 12,
        'homogeneous_W_weights': current_weights,
        'remainder_transfer': 'if quotient defect=G^2 R then physical defect=F^2 J R pulled back',
        'scope': 'Conditional exact source and vector-field transfer. No rational current or certificate is asserted.'
    }
    path = Path(__file__).with_name('piola-transfer-results.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
