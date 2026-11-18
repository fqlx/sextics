"""Reproduce the 33-dimensional full matrix algebra certificate with Python 3."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse
import re


SQUARE = 4
H_INDICES = (8, 17, 19, 22, 25, 27, 29)
COLUMN_INDICES = tuple(i for i in range(35) if i not in (4, 29, 34))
ELL = {8: 3, 16: -3, 18: -1, 23: 2, 25: 1, 29: -1, 31: 2}
EXPECTED_DETERMINANT = -333002129772277037540987257626384275757114307214929177870336


def bases():
    # Exponent bounds in the actual weighted Fermat Jacobian algebra.
    monomials = [c for c in product(*(range(k + 1) for k in (4, 4, 4, 4, 1)))
                 if sum(c) + c[4] == 6]
    def character(c):
        return (2*c[0] + 2*c[1] + c[2]) % 3
    return ([c for c in monomials if character(c) == 1],
            [c for c in monomials if character(c) == 0])


def compare_lean(lean, columns, tangents):
    source = lean.read_text()
    for name, table in [('basisMonomial', columns), ('tangentMonomial', tangents)]:
        body = source.split('def ' + name + ' :', 1)[1].split('\ndef ', 1)[0]
        supplied = [tuple(map(int, row.split(','))) for row in re.findall(r'!\[([\d, ]+)\]', body)]
        assert supplied == table, f'{name} order differs from the enumerated basis'
    expected = list(product(range(len(tangents)), range(len(columns))))
    body = source.split('def complement :', 1)[1].split('\n\ntheorem ', 1)[0]
    rows = re.findall(r'!\[((?:(?:none|some \d+)(?:, )?)+)\]', body)
    assert len(rows) == len(tangents)
    supplied = [[None if x == 'none' else int(x.split()[1]) for x in row.split(', ')] for row in rows]
    for t, r in expected:
        target = tuple(s-a-b for s,a,b in zip((4,4,4,4,1), tangents[t], columns[r]))
        assert supplied[t][r] == (columns.index(target) if target in columns else None)


def matrix_family(b, t):
    socle = (4, 4, 4, 4, 1)
    return [[[int(all(u+v+w == z for u,v,w,z in zip(x,y,m,socle))) for y in b] for x in b]
            for m in t]


def matrix_mul(a, b):
    columns = list(zip(*b))
    return [[sum(x*y for x,y in zip(row,col)) for col in columns] for row in a]


def matvec(a, b):
    return [sum(x*y for x,y in zip(row,b)) for row in a]


def det_adjugate(matrix):
    size = len(matrix)
    data = [[Fraction(x) for x in row] + [Fraction(i == j) for j in range(size)]
            for i, row in enumerate(matrix)]
    det = Fraction(1)
    for i in range(size):
        j = next((j for j in range(i, size) if data[j][i]), None)
        if j is None:
            raise AssertionError(f'singular matrix at column {i}')
        if j != i:
            data[i], data[j] = data[j], data[i]
            det = -det
        pivot = data[i][i]
        det *= pivot
        data[i] = [x / pivot for x in data[i]]
        for j in range(size):
            if j != i and data[j][i]:
                factor = data[j][i]
                data[j] = [x - factor*y for x,y in zip(data[j],data[i])]
    assert det.denominator == 1
    result = [[det*x for x in row[size:]] for row in data]
    assert all(x.denominator == 1 for row in result for x in row)
    return int(det), [[int(x) for x in row] for row in result]


def verify(lean=None):
    b, t = bases()
    assert (len(b), len(t)) == (33, 35)
    if lean is not None:
        compare_lean(lean, b, t)
    family = matrix_family(b, t)
    h = [[sum(family[k][i][j] for k in H_INDICES) for j in range(33)] for i in range(33)]
    det_h, adj_h = det_adjugate(h)
    assert det_h == -24
    assert matrix_mul(h, adj_h) == [[det_h*int(i == j) for j in range(33)] for i in range(33)]
    ell = [ELL.get(i, 0) for i in range(33)]
    square = matrix_mul(matrix_mul(family[SQUARE], adj_h), family[SQUARE])
    assert square == [[x*y for y in ell] for x in ell]
    adj_ell = matvec(adj_h, ell)
    ct = [ell] + [matvec(family[i], adj_ell) for i in COLUMN_INDICES]
    det_c, _ = det_adjugate(ct)
    assert det_c == EXPECTED_DETERMINANT
    print('Fermat Higgs matrices:',len(t),'of size',len(b))
    print('det(H) =',det_h)
    print('theta[4] adj(H) theta[4] = ell ell^T')
    print('det(C) =',det_c)
    print('det(H), det(C) modulo 7 =',det_h%7,det_c%7)
    print('Independent matrix words:',len(ct)**2)
    return family, h, adj_h, ell, ct


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, help='compare monomials and all 1,155 complement rows with GeometricFormalInputs01Part01.lean')
    verify(parser.parse_args().lean)
