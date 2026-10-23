"""Compare the C++ solver with independent dense elimination on small systems.

Run after compiling solve_sparse.cpp: python3 selftest_solver.py
The eight systems include consistent/inconsistent and dependent-column cases.
No production matrix or source file is changed.
"""
import json
import random
import struct
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def dense_rank(matrix, prime):
    a = [row[:] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((r for r in range(rank, len(a)) if a[r][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        scale = pow(a[rank][col], -1, prime)
        a[rank] = [x * scale % prime for x in a[rank]]
        for row in range(rank + 1, len(a)):
            scale = a[row][col]
            if scale:
                a[row] = [(x - scale * y) % prime
                          for x, y in zip(a[row], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def write_binary(path, matrix, rhs, prime):
    m, n = len(matrix), len(matrix[0])
    with path.open('wb') as out:
        out.write(struct.pack('<IIII', m, n, prime,
                              sum(bool(v) for row in matrix for v in row)))
        for col in range(n + 1):
            entries = [(row, rhs[row] if col == n else matrix[row][col])
                       for row in range(m)
                       if (rhs[row] if col == n else matrix[row][col])]
            out.write(struct.pack('<I', len(entries)))
            for entry in entries:
                out.write(struct.pack('<II', *entry))


def main():
    reports = []
    with tempfile.TemporaryDirectory(prefix='sparse-solver-audit-') as tmp:
        tmp = Path(tmp)
        for seed in range(8):
            rng = random.Random(seed)
            m, n, prime = 35, 20, 1009
            matrix = [[rng.randrange(prime) if rng.random() < .2 else 0
                       for _ in range(n)] for _ in range(m)]
            if seed >= 4:
                for row in matrix:
                    row[-1] = (row[0] + row[1]) % prime
                    row[-2] = 0
            witness = [rng.randrange(prime) for _ in range(n)]
            rhs = [sum(x * y for x, y in zip(row, witness)) % prime
                   for row in matrix]
            if seed % 2:
                row = rng.randrange(m)
                rhs[row] = (rhs[row] + 1) % prime
            binary, output = tmp / f'{seed}.bin', tmp / f'{seed}.json'
            write_binary(binary, matrix, rhs, prime)
            subprocess.run([str(ROOT / 'solve_sparse'), str(binary),
                            str(output), '30', '1000'],
                           check=True, capture_output=True)
            actual = json.loads(output.read_text())
            rank = dense_rank(matrix, prime)
            augmented_rank = dense_rank([row + [b] for row, b in zip(matrix, rhs)], prime)
            assert actual['complete_rank'] and actual['rank'] == rank
            assert actual['contradiction'] == (augmented_rank > rank)
            if not actual['contradiction']:
                solution = actual['solution']
                assert all(sum(x * y for x, y in zip(row, solution)) % prime == b
                           for row, b in zip(matrix, rhs))
            reports.append({'seed': seed, 'rank': rank,
                            'augmented_rank': augmented_rank,
                            'solution_verified': not actual['contradiction']})
    print(json.dumps({'status': 'all_eight_passed', 'cases': reports}, indent=2))


if __name__ == '__main__':
    main()
