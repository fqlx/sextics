#!/usr/bin/env python3
"""Independent rank/consistency and numerical-bound audit of blocked F_p solver.

Systems have known rank and consistency from invertible row/column operations.
This tests numerical correctness, including nearly maximal exact BLAS sums,
rather than copying the solver's elimination implementation.
"""
from pathlib import Path
import sys
import json
import hashlib
import importlib.util
import numpy as np


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def is_prime(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    q = 3
    while q*q <= p:
        if p % q == 0:
            return False
        q += 2
    return True


def known_system(m, n, rank, p, rng, inconsistent):
    assert 0 <= rank <= min(m, n)
    assert not inconsistent or rank < m
    a = np.zeros((m, n), dtype=np.int64)
    for i in range(rank):
        a[i, n-rank+i] = 1  # Leading zero columns stress skipped panels.
    rhs = np.zeros(m, dtype=np.int64)
    if inconsistent:
        rhs[rank] = 1
    aug = np.column_stack((a, rhs))
    # These operations preserve rank(A) and augmented-rank difference.
    for _ in range(3*m):
        if m < 2:
            break
        i, j = rng.choice(m, size=2, replace=False)
        coefficient = int(rng.integers(1, p))
        aug[i] = (aug[i] + coefficient*aug[j]) % p
        if rng.integers(0, 3) == 0:
            aug[[i, j]] = aug[[j, i]]
    a, rhs = aug[:, :n].copy(), aug[:, n].copy()
    for _ in range(3*n):
        if n < 2:
            break
        i, j = rng.choice(n, size=2, replace=False)
        coefficient = int(rng.integers(1, p))
        a[:, i] = (a[:, i] + coefficient*a[:, j]) % p
        if rng.integers(0, 3) == 0:
            a[:, [i, j]] = a[:, [j, i]]
    # Add a nontrivial vector in the column space to either RHS.
    x = rng.integers(0, p, size=n, dtype=np.int64)
    rhs = (rhs+a@x) % p
    return a, rhs


def exact_residual(a, x, rhs, p):
    return [sum(int(c)*int(v) for c, v in zip(row, x)) % p-int(b)
            for row, b in zip(a, rhs)]


def main():
    endpoint = Path(__file__).resolve().parent.parent/'endpoint'
    blocked_path = endpoint/'additive/block_modular.py'
    sys.path.insert(0, str(endpoint))
    blocked = load(blocked_path, 'audited_block_modular')
    reference = load(endpoint/'two_pole_infinity_current_search.py', 'old_modular_reference')
    stress_prime = 13_500_001
    while not is_prime(stress_prime):
        stress_prime += 2
    primes = [2, 101, 1009, 1_000_003, stress_prime]
    for p in primes:
        assert is_prime(p)
    rng = np.random.default_rng(94817263)
    cases = []
    comparisons = []
    dimensions = [(0, 0, 0), (0, 4, 0), (4, 0, 0), (5, 7, 0),
                  (4, 9, 3), (9, 4, 3), (28, 35, 19),
                  (55, 70, 48), (85, 63, 51), (120, 140, 90)]
    for p in primes:
        for m, n, rank in dimensions:
            for inconsistent in [False, True] if rank < m else [False]:
                a, rhs = known_system(m, n, rank, p, rng, inconsistent)
                cases.append((f'known-rank-{m}-{n}-{rank}-{inconsistent}', a, rhs, p, rank, inconsistent))

    # Every entry of the delayed BLAS product is 48*(p-1)^2, close to
    # 2^53 for the stress prime. This exercises the maximal negative update.
    for p in [1009, 1_000_003, stress_prime]:
        k = 48
        a = np.zeros((k+4, k+3), dtype=np.int64)
        a[:k, :k] = np.eye(k, dtype=np.int64)
        a[:k, k:] = p-1
        a[k:, :k] = p-1
        x = rng.integers(0, p, size=a.shape[1], dtype=np.int64)
        rhs = a@x % p
        cases.append(('maximal-positive-BLAS-sum', a.copy(), rhs.copy(), p, k+1, False))
        rhs[-1] = (rhs[-1]+1) % p
        cases.append(('maximal-positive-BLAS-sum-inconsistent', a.copy(), rhs.copy(), p, k+1, True))

        # A unit lower triangular panel makes each pivot-row delayed update
        # subtract j*(p-1)^2. Its exact normalized trailing entries are p-1.
        a = np.zeros((k, k+2), dtype=np.int64)
        for i in range(k):
            a[i, :i] = p-1
            a[i, i] = 1
            a[i, k:] = (i-1) % p
        x = rng.integers(0, p, size=a.shape[1], dtype=np.int64)
        cases.append(('maximal-pivot-row-delayed-sum', a, a@x % p, p, k, False))

    for name, a, rhs, p, expected_rank, inconsistent in cases:
        n = a.shape[1]
        assert n*(p-1)**2 < 2**63
        old_rank, old_solution = reference.solve_mod(a, rhs, p)
        assert old_rank == expected_rank, (name, p, old_rank, expected_rank)
        assert (old_solution is None) == inconsistent, (name, p, 'old consistency')
        if old_solution is not None:
            assert all(x == 0 for x in exact_residual(a, old_solution, rhs, p))
        for panel in [1, 7, 17, 48]:
            assert panel*(p-1)**2 < 2**53
            rank, solution = blocked.solve_mod(a, rhs, p, panel_size=panel)
            assert rank == expected_rank == old_rank, (name, p, panel, 'rank')
            assert (solution is None) == inconsistent, (name, p, panel, 'consistency')
            if solution is not None:
                # Python integers avoid relying on the solver's int64 verifier.
                assert all(x == 0 for x in exact_residual(a, solution, rhs, p)), (name, p, panel, 'residual')
            comparisons.append({'case': name, 'shape': list(a.shape), 'prime': p,
                                'panel': panel, 'rank': rank, 'inconsistent': inconsistent})
    result = {
        'status': 'passed',
        'solver_sha256': hashlib.sha256(blocked_path.read_bytes()).hexdigest(),
        'cases': len(cases), 'comparisons': len(comparisons), 'primes': primes,
        'panel_sizes': [1, 7, 17, 48],
        'oracle': 'Known rank and consistency from invertible transformations; comparison with old int64 modular routine; solutions checked with Python integer dot products.',
        'stress_float_dot': 48*(stress_prime-1)**2,
        'float_exact_integer_limit': 2**53,
        'current_run_bound_p1009_n2740': {'float_panel_dot': 48*1008**2,
                                        'int64_solution_dot': 2740*1008**2},
        'required_bounds': ['panel_size*(p-1)^2 < 2^53',
                            'n*(p-1)^2 < 2^63 for int64 back-substitution and final verification',
                            'canonical integral mat,rhs values in [0,p)'],
        'comparisons_detail': comparisons,
        'scope': 'Numerical finite-field linear algebra audit only. Evaluation consistency is not an exact rational current or certificate.'
    }
    path = Path(__file__).with_name('block-modular-audit-results.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'comparisons_detail'}, indent=2))


if __name__ == '__main__':
    main()
