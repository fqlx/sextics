#!/usr/bin/env python3
"""Independent exact conic-log source identities and modular column spot audit."""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys
import hashlib
import importlib.util
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent/'quotient'))
from verify_piola_transfer import LaurentRing


def evaluate(poly, values, p):
    result = 0
    for exponent, c in poly.items():
        term = c.numerator*pow(c.denominator, -1, p) % p
        for value, power in zip(values, exponent):
            term = term*pow(int(value), power, p) % p
        result = (result+term) % p
    return result


def main():
    x = LaurentRing(['x', 'y', 'z'])
    H = x.poly('1+x**6+y**6+z**6+x*y*z/2')
    C = x.poly('x**3*z/2+x*y/3')
    s = x.poly('-3*z/2')
    L = x.add(H, x.mul(s, C))
    Fpole = x.add(x.power(L, 2), x.scale(x.power(s, 6), -4))
    lam = [x.add(x.diff(L, q), x.scale(x.mul(L, x.laurent('1/z')), -3) if q == 'z' else {})
           for q in x.names]
    checks, multipliers = [], []
    for j, name in enumerate(x.names):
        dlog = [{}, {}, {}]
        dlog[j] = x.laurent('1/'+name)
        V = [x.add(x.mul(lam[(i+1)%3], dlog[(i+2)%3]),
                   x.scale(x.mul(lam[(i+2)%3], dlog[(i+1)%3]), -1))
             for i in range(3)]
        apply = lambda poly: x.add(*(x.mul(v, x.diff(poly, q)) for v, q in zip(V, x.names)))
        div = x.add(*(x.diff(v, q) for v, q in zip(V, x.names)))
        A = x.mul(V[2], x.laurent('1/z'))
        for label, residual in [
            ('conic_tangent', x.add(apply(L), x.scale(x.mul(L, A), -3))),
            ('residue_divergence', x.add(div, x.scale(A, -3))),
            ('finite_residue_closed', x.add(apply(Fpole), x.scale(x.mul(Fpole, div), -2)))]:
            assert not residual, (name, label, residual)
            checks.append(name+'_'+label)
        K = x.add(apply(C), x.scale(x.mul(C, A), -2))
        multipliers.append(K)

    r = Ring(['p', 'H', 'C', 'r', 'A', 'Q'])
    f = r.poly('(H+C*p)**2-4*p**6')
    S = r.poly('H+C*p')
    d = r.poly('p-r')
    VH = r.poly('A*(3*H+2*r*C)-r*Q')
    lhs = r.add(r.scale(r.mul(VH, r.mul(S, d)), -1),
        r.scale(r.mul(r.var('Q'), r.mul(r.var('p'), r.mul(S, d))), -1),
        r.mul(r.poly('r*A'), f), r.mul(r.poly('3*A'), r.mul(f, d)))
    rhs = r.add(r.scale(r.mul(r.poly('Q-2*C*A'), r.mul(S, r.power(d, 2))), -1),
        r.mul(r.var('A'), r.add(r.mul(r.var('r'), f),
              r.scale(r.mul(r.var('p'), r.mul(d, r.diff(f, 'p'))), Q(1, 2)))))
    assert not r.add(lhs, r.scale(rhs, -1))
    checks.append('raw_source_plus_vertical_exact')

    endpoint = Path(__file__).resolve().parent.parent/'endpoint'
    data = json.loads((endpoint/'reconstructed-connection.json').read_text())
    connection_ring = Ring(['p', 'H', 'C'])
    pairs = [connection_ring.rational(text) for text in data['H']['columns'][0]]
    script_path = endpoint/'additive/merged_log_residue.py'
    sys.path.insert(0, str(script_path.parent))
    spec = importlib.util.spec_from_file_location('audited_log_columns', script_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    p = 1009
    rng = np.random.default_rng(582910)
    points, expected_mh = [], []
    while len(points) < 24:
        point = tuple(int(a) for a in rng.integers(1, p, size=3))
        hv, cv = evaluate(H, point, p), evaluate(C, point, p)
        if not hv or not (4*pow(cv, 6, p)-729*pow(hv, 4, p)) % p:
            continue
        if any(not ((hv+cv*r0)**2-4*pow(r0, 6, p)) % p
               for r0 in [(-3*point[2]*pow(2, -1, p)) % p,
                          (-point[1]*pow(point[0], -2, p)) % p]):
            continue
        compact = [evaluate(num, (0, hv, cv), p)*pow(evaluate(den, (0, hv, cv), p), -1, p) % p
                   for num, den in pairs]
        points.append(point)
        expected_mh.append([compact[0], compact[1], 0, compact[2], compact[3]])
    points = np.array(points, dtype=np.int64)
    expected_mh = np.array(expected_mh, dtype=np.int64)
    source = np.array([(-pow(int(point[1]), 3, p)*pow(6, -1, p)*row) % p
                       for point, row in zip(points, expected_mh)], dtype=np.int64).reshape(-1)
    observed = module.log_columns(points, p, source)
    expected = np.column_stack([
        np.array([(evaluate(K, tuple(point), p)*row) % p
                  for point, row in zip(points, expected_mh)], dtype=np.int64).reshape(-1)
        for K in multipliers])
    assert np.array_equal(observed, expected)
    checks.append('implemented_columns_24_generic_points')
    result = {'status': 'passed', 'arithmetic': 'exact Fraction Laurent-polynomial identities, plus independent finite-field column comparison',
        'checks': checks, 'prime': p, 'generic_points': len(points),
        'script_sha256': hashlib.sha256(script_path.read_bytes()).hexdigest(),
        'source_transport': 'source=-y^3 M_H e0/6; multiplying by -6/y^3 recovers exactly the reordered M_H e0. Each added column is K_g M_H e0.',
        'vertical_correction': '-V(s)/s * d_p[p/((p-s)Z)] must be retained when constructing the literal primitive',
        'scope': 'Valid additional rational residue-current columns only. No certificate and no exact exclusion follows from the modular no-hit.'}
    path = Path(__file__).with_name('log-residue-columns-audit-results.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
