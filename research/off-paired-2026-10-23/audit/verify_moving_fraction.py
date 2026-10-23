#!/usr/bin/env python3
"""Independently replay finite moving-pole Dwork identities with Fraction.

Imports only the independently written polynomial arithmetic, not the SymPy
generator. No rational current or certificate is asserted.
"""
import hashlib
import json
from pathlib import Path
from verify_connection_fraction import Ring

root = Path(__file__).resolve().parent.parent
data_path = root / 'endpoint/moving-pole-connection.json'
data = json.loads(data_path.read_text())
ring = Ring(['p', 'H', 'C', 'r'])
f = ring.poly('(H+C*p)**2-4*p**6')
fp = ring.diff(f, 'p')
K = ring.poly('H*(4*C**6-729*H**4)*((H+C*r)**2-4*r**6)')
d = ring.poly('p-r')
d2 = ring.power(d, 2)
checks = {}


def check(name, polynomial):
    assert not polynomial, name
    checks[name] = True


for v in ['H', 'C', 'r']:
    columns = [ring.cleared(x, K) for x in data['columns'][v]]
    compact = ring.add(*(ring.mul(a, ring.poly(f'p**{j}'))
                         for a, j in zip(columns[:4], data['basis'])))
    if v != 'r':
        R = ring.cleared(data['exact_primitives'][v], K)
        check(f'moving_Dwork_{v}', ring.add(
            ring.scale(ring.mul(K, ring.diff(f, v)), -1),
            ring.scale(ring.mul(columns[4], f), -2),
            ring.scale(ring.mul(ring.mul(d, f), compact), -2),
            ring.scale(ring.mul(ring.mul(d, f), ring.diff(R, 'p')), -2),
            ring.mul(ring.mul(d, fp), R)))
    else:
        T = ring.cleared(data['exact_primitives'][v], ring.mul(K, d))
        check('moving_Dwork_r', ring.add(
            ring.scale(ring.mul(K, f), 2),
            ring.scale(ring.mul(ring.mul(columns[4], f), d), -2),
            ring.scale(ring.mul(ring.mul(d2, f), compact), -2),
            ring.scale(ring.mul(f, ring.add(
                ring.mul(ring.diff(T, 'p'), d), ring.scale(T, -1))), -2),
            ring.mul(ring.mul(fp, T), d)))

# Literal source identity, including its residue coefficient and exact part.
check('literal_source_numerator', ring.add(
    ring.diff(f, 'C'),
    ring.scale(ring.mul(ring.var('r'), ring.diff(f, 'H')), -1),
    ring.scale(ring.mul(d, ring.diff(f, 'H')), -1)))
compact = json.loads((root / 'endpoint/reconstructed-connection.json').read_text())
for j in range(5):
    lhs = ring.add(ring.cleared(data['columns']['C'][j], K),
                   ring.scale(ring.mul(ring.var('r'),
                              ring.cleared(data['columns']['H'][j], K)), -1))
    rhs = ring.cleared(compact['H']['columns'][0][j], K) if j < 4 else {}
    check(f'source_connection_column_{j}', ring.add(lhs, ring.scale(rhs, -1)))

result = {
    'status': 'passed',
    'arithmetic': 'independent standard-library Fraction polynomial dictionaries',
    'data_sha256': hashlib.sha256(data_path.read_bytes()).hexdigest(),
    'checks': checks,
    'scope': 'Exact moving-pole connection/source identities; no current, certificate, Lean proof, or acceptance.'
}
(Path(__file__).with_name('moving-fraction-results.json')).write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
