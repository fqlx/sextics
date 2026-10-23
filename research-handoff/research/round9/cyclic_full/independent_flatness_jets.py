"""Independent finite-prime first-jet audit of saved transverse matrices."""
import hashlib
import json
import pickle
import random
import time
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
PRIME = 1000003


def polynomial_terms(expr, symbols):
    return [(e, int(c.p)*pow(int(c.q), -1, PRIME) % PRIME)
            for e, c in sp.Poly(expr, *symbols, domain=sp.QQ).terms()]


def jet(poly, point):
    value, derivative = 0, [0, 0, 0]
    for exponents, coefficient in poly:
        monomial = coefficient
        for x, exponent in zip(point, exponents):
            monomial = monomial*pow(x, exponent, PRIME) % PRIME
        value = (value+monomial) % PRIME
        for j, exponent in enumerate(exponents):
            if exponent:
                derivative[j] = (derivative[j]+monomial*exponent*pow(point[j], -1, PRIME)) % PRIME
    return value, derivative


def rational_jet(pair, point):
    numerator, nd = jet(pair[0], point)
    denominator, dd = jet(pair[1], point)
    if not denominator:
        raise ZeroDivisionError
    inverse = pow(denominator, -1, PRIME)
    return (numerator*inverse % PRIME,
            [(n*denominator-numerator*d)*inverse**2 % PRIME for n, d in zip(nd, dd)])


def multiply(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(3)) % PRIME
             for j in range(3)] for i in range(3)]


def main():
    started = time.monotonic()
    rng = random.Random(94613)
    reports = []
    for name in ('actual_fast', 'conjugate_fast'):
        path = HERE/(name+'.pickle')
        data = pickle.loads(path.read_bytes())
        symbols = data['symbols'][3:]
        blocks = []
        for symbol in symbols:
            matrix = data['connection'][str(symbol)]
            block = []
            for i in range(3):
                row = []
                for j in range(3):
                    num, den = sp.fraction(matrix[i, j])
                    row.append((polynomial_terms(num, symbols), polynomial_terms(den, symbols)))
                block.append(row)
            blocks.append(block)
        checked, rejected = [], 0
        while len(checked) < 25:
            point = [rng.randrange(2, PRIME) for _ in range(3)]
            try:
                jets = [[[[*rational_jet(pair, point)] for pair in row] for row in block] for block in blocks]
            except ZeroDivisionError:
                rejected += 1
                continue
            values = [[[entry[0] for entry in row] for row in block] for block in jets]
            for a, b in ((0, 1), (0, 2), (1, 2)):
                ba = multiply(values[b], values[a])
                ab = multiply(values[a], values[b])
                curvature = [[(jets[b][i][j][1][a]-jets[a][i][j][1][b]+ba[i][j]-ab[i][j]) % PRIME
                              for j in range(3)] for i in range(3)]
                assert curvature == [[0]*3 for _ in range(3)], (name, point, a, b, curvature)
            checked.append(point)
        reports.append({'packet': path.name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'good_points': checked, 'bad_points_skipped': rejected,
                        'all_three_curvature_pairs_zero': True})
    out = {'prime': PRIME, 'reports': reports,
           'convention': 'partial_i N_j-partial_j N_i+N_j N_i-N_i N_j',
           'seconds': time.monotonic()-started,
           'scope': 'Independent finite-prime analytic first-jet diagnostic; not a characteristic-zero identity or certificate.'}
    (HERE/'independent_flatness_jets.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k != 'reports'}, indent=2))


if __name__ == '__main__':
    main()
