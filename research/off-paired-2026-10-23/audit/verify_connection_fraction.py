#!/usr/bin/env python3
"""Independent exact audit of endpoint data; Python standard library only.

This imports neither the connection generator nor its SymPy verifier. It parses
the submitted rational expressions with ast, clears one fixed denominator, and
checks coefficient dictionaries using Fraction arithmetic.
"""
import argparse
import ast
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


class Ring:
    def __init__(self, names):
        self.names = tuple(names)
        self.zero_exp = (0,) * len(names)

    def const(self, a):
        return {self.zero_exp: Q(a)} if a else {}

    def var(self, name):
        return {tuple(int(i == self.names.index(name))
                      for i in range(len(self.names))): Q(1)}

    def add(self, *args):
        result = {}
        for a in args:
            for e, c in a.items():
                result[e] = result.get(e, Q(0)) + c
                if not result[e]:
                    del result[e]
        return result

    def scale(self, a, c):
        c = Q(c)
        return {e: x*c for e, x in a.items() if x*c}

    def mul(self, a, b):
        result = {}
        for e, c in a.items():
            for f, d in b.items():
                g = tuple(x+y for x, y in zip(e, f))
                result[g] = result.get(g, Q(0)) + c*d
                if not result[g]:
                    del result[g]
        return result

    def power(self, a, n):
        assert isinstance(n, int) and n >= 0
        result = self.const(1)
        while n:
            if n & 1:
                result = self.mul(result, a)
            n >>= 1
            if n:
                a = self.mul(a, a)
        return result

    def diff(self, a, name):
        i = self.names.index(name)
        result = {}
        for e, c in a.items():
            if e[i]:
                f = e[:i] + (e[i]-1,) + e[i+1:]
                result[f] = c*e[i]
        return result

    def exact_div(self, a, b):
        assert b, 'zero denominator'
        remainder, quotient = dict(a), {}
        f = max(b)
        while remainder:
            e = max(remainder)
            assert all(x >= y for x, y in zip(e, f)), 'not polynomial'
            g = tuple(x-y for x, y in zip(e, f))
            c = remainder[e]/b[f]
            term = {g: c}
            quotient = self.add(quotient, term)
            remainder = self.add(remainder,
                                 self.scale(self.mul(term, b), -1))
        return quotient

    def rational(self, text):
        def visit(node):
            if isinstance(node, ast.Constant):
                assert type(node.value) is int
                return self.const(node.value), self.const(1)
            if isinstance(node, ast.Name):
                assert node.id in self.names
                return self.var(node.id), self.const(1)
            if isinstance(node, ast.UnaryOp):
                a, b = visit(node.operand)
                if isinstance(node.op, ast.USub):
                    return self.scale(a, -1), b
                assert isinstance(node.op, ast.UAdd)
                return a, b
            assert isinstance(node, ast.BinOp)
            if isinstance(node.op, ast.Pow):
                assert isinstance(node.right, ast.Constant)
                n = node.right.value
                assert type(n) is int and n >= 0
                a, b = visit(node.left)
                return self.power(a, n), self.power(b, n)
            a, b = visit(node.left)
            c, d = visit(node.right)
            if isinstance(node.op, ast.Add):
                return self.add(self.mul(a, d), self.mul(c, b)), self.mul(b, d)
            if isinstance(node.op, ast.Sub):
                return self.add(self.mul(a, d), self.scale(self.mul(c, b), -1)), self.mul(b, d)
            if isinstance(node.op, ast.Mult):
                return self.mul(a, c), self.mul(b, d)
            assert isinstance(node.op, ast.Div) and c
            return self.mul(a, d), self.mul(b, c)
        return visit(ast.parse(text, mode='eval').body)

    def poly(self, text):
        a, b = self.rational(text)
        return self.exact_div(a, b)

    def cleared(self, text, denominator):
        a, b = self.rational(text)
        return self.exact_div(self.mul(a, denominator), b)

    def subst(self, a, values, target):
        result = {}
        for e, c in a.items():
            term = target.const(c)
            for n, k in zip(self.names, e):
                term = target.mul(term, target.power(values[n], k))
            result = target.add(result, term)
        return result


def record(path):
    raw = path.read_bytes()
    fields = dict(line.split(': ', 1) for line in raw.decode().splitlines()
                  if line.startswith(('F: ', 'A: ', 'q: ')))
    return raw, fields


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--connection', type=Path,
                        default=Path(__file__).parent.parent/'endpoint/reconstructed-connection.json')
    parser.add_argument('--target', type=Path,
                        default=Path('/workspace/off-paired-sextics/data/off-paired/instance.rec'))
    parser.add_argument('--original', type=Path,
                        default=Path('/workspace/sextics/data/off-paired/instance.rec'))
    parser.add_argument('--third-kind', type=Path,
                        default=Path(__file__).parent.parent/'endpoint/third-kind-connection.json')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('connection-fraction-results.json'))
    args = parser.parse_args()
    data = json.loads(args.connection.read_text())
    third = json.loads(args.third_kind.read_text())
    assert data['basis'] == [0, 1, 3, 4]
    assert third['basis'] == data['basis'] and third['new_basis_index'] == 2
    ring = Ring(['p', 'H', 'C'])
    f = ring.poly('(H+C*p)**2-4*p**6')
    assert ring.poly(data['f']) == f
    L = ring.poly('4*H*(4*C**6-729*H**4)')
    mats = {v: [[ring.cleared(data[v]['columns'][j][i], L)
                 for j in range(4)] for i in range(4)]
            for v in ['H', 'C']}
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)

    # d_v(p^j dp/Z) = sum_i M_v[i,j] p^basis[i] dp/Z + d_p(R_v,j/Z).
    # Clear L Z^3 to obtain an ordinary exact polynomial identity.
    for v in ['H', 'C']:
        for j, power in enumerate(data['basis']):
            R = {}
            for k, text in enumerate(data[v]['primitives'][j]):
                R = ring.add(R, ring.mul(ring.cleared(text, L), ring.poly(f'p**{k}')))
            res = ring.scale(ring.mul(L, ring.mul(ring.poly(f'p**{power}'), ring.diff(f, v))), Q(-1, 2))
            for i, basis_power in enumerate(data['basis']):
                res = ring.add(res, ring.scale(ring.mul(mats[v][i][j],
                    ring.mul(ring.poly(f'p**{basis_power}'), f)), -1))
            res = ring.add(res, ring.scale(ring.mul(ring.diff(R, 'p'), f), -1),
                           ring.scale(ring.mul(R, ring.diff(f, 'p')), Q(1, 2)))
            check(f'Dwork_{v}_{power}', res)

    for i, power in enumerate(data['basis']):
        for j in range(4):
            res = ring.add(ring.scale(ring.mul(ring.var('H'), mats['H'][i][j]), 6),
                           ring.scale(ring.mul(ring.var('C'), mats['C'][i][j]), 4),
                           ring.scale(L, -(2*power-4) if i == j else 0))
            check(f'Euler_{i}_{j}', res)

    # Connection acts on coefficient columns. Flatness is
    # partial_H M_C - partial_C M_H + M_H M_C - M_C M_H = 0.
    for i in range(4):
        for j in range(4):
            res = ring.add(ring.mul(ring.diff(mats['C'][i][j], 'H'), L),
                           ring.scale(ring.mul(mats['C'][i][j], ring.diff(L, 'H')), -1),
                           ring.scale(ring.mul(ring.diff(mats['H'][i][j], 'C'), L), -1),
                           ring.mul(mats['H'][i][j], ring.diff(L, 'C')))
            for k in range(4):
                res = ring.add(res,
                    ring.mul(mats['H'][i][k], mats['C'][k][j]),
                    ring.scale(ring.mul(mats['C'][i][k], mats['H'][k][j]), -1))
            check(f'flatness_{i}_{j}', res)

    # Add omega_2, the third-kind differential with constant residues at
    # the two infinity sections. Its derivatives have no omega_2 component.
    third_cols = {v: [ring.cleared(text, L) for text in third['columns'][v]]
                  for v in ['H', 'C']}
    for v in ['H', 'C']:
        R = {}
        for k, text in enumerate(third['primitives'][v]):
            R = ring.add(R, ring.mul(ring.cleared(text, L), ring.poly(f'p**{k}')))
        res = ring.scale(ring.mul(L, ring.mul(ring.poly('p**2'), ring.diff(f, v))), Q(-1, 2))
        for i, basis_power in enumerate(data['basis']):
            res = ring.add(res, ring.scale(ring.mul(third_cols[v][i],
                ring.mul(ring.poly(f'p**{basis_power}'), f)), -1))
        res = ring.add(res, ring.scale(ring.mul(ring.diff(R, 'p'), f), -1),
                       ring.scale(ring.mul(R, ring.diff(f, 'p')), Q(1, 2)))
        check(f'third_Dwork_{v}_2', res)
    for i in range(4):
        check(f'third_Euler_{i}', ring.add(
            ring.scale(ring.mul(ring.var('H'), third_cols['H'][i]), 6),
            ring.scale(ring.mul(ring.var('C'), third_cols['C'][i]), 4)))
        res = ring.add(ring.mul(ring.diff(third_cols['C'][i], 'H'), L),
                       ring.scale(ring.mul(third_cols['C'][i], ring.diff(L, 'H')), -1),
                       ring.scale(ring.mul(ring.diff(third_cols['H'][i], 'C'), L), -1),
                       ring.mul(third_cols['H'][i], ring.diff(L, 'C')))
        for k in range(4):
            res = ring.add(res,
                ring.mul(mats['H'][i][k], third_cols['C'][k]),
                ring.scale(ring.mul(mats['C'][i][k], third_cols['H'][k]), -1))
        check(f'third_flatness_{i}', res)

    # At u=1/p, write Z=u^-3 V. V^2=-4+C^2 u^4+2HC u^5+H^2 u^6.
    # There are no u,u^2,u^3 terms. Thus V^-1 = s^-1 + O(u^4),
    # s^2=-4. Only omega_2=-u^-1 du/V has a residue, namely -1/s,
    # independent of H,C; parameter derivatives have zero residues.
    infinity = Ring(['u', 'H', 'C'])
    infinity_f = infinity.poly('-4+C**2*u**4+2*H*C*u**5+H**2*u**6')
    assert infinity_f.get((0, 0, 0)) == -4
    for power in [1, 2, 3]:
        assert all(e[0] != power for e in infinity_f)
    for v in ['H', 'C']:
        assert all(e[0] >= 4 for e in infinity.diff(infinity_f, v))
    checks.append('third_constant_infinity_residues')

    # Independent weighted-gauge check after H=lambda^3, C=t*lambda^2.
    # If B(t)=M_C(1,t), then
    # M_C[i,j]=lambda^(basis[j]-basis[i]-2) B(t)[i,j].
    weighted = Ring(['ell', 't', 'u'])
    values = {'p': weighted.var('u'),
              'H': weighted.poly('ell**3'),
              'C': weighted.poly('t*ell**2')}
    unit_values = {'p': weighted.var('u'), 'H': weighted.const(1),
                   'C': weighted.var('t')}
    for i, row_power in enumerate(data['basis']):
        for j, column_power in enumerate(data['basis']):
            actual = ring.subst(mats['C'][i][j], values, weighted)
            expected = weighted.mul(
                weighted.poly(f'ell**{13+column_power-row_power}'),
                ring.subst(mats['C'][i][j], unit_values, weighted))
            check(f'weighted_C_gauge_{i}_{j}',
                  weighted.add(actual, weighted.scale(expected, -1)))
    check('weighted_curve', weighted.add(
        ring.subst(f, values | {'p': weighted.poly('ell*u')}, weighted),
        weighted.scale(weighted.poly('ell**6*((1+t*u)**2-4*u**6)'), -1)))
    check('weighted_discriminant', weighted.add(
        ring.subst(ring.poly('4*C**6-729*H**4'), values, weighted),
        weighted.scale(weighted.poly('ell**12*(4*t**6-729)'), -1)))

    physical = Ring(['X0', 'X1', 'X2', 'Y0', 'Y1', 'Y2'])
    raw, fields = record(args.target)
    original_raw, original = record(args.original)
    F = physical.poly(fields['F'])
    A = physical.poly(fields['A'])
    expected_F = physical.poly('X0**6+X1**6+X2**6+Y0**6+Y1**6+Y2**6+'
                              'X0**3*X1*Y0*Y1/2+X1**3*X2*Y1*Y2/2+'
                              'X0**2*X1*X2*Y0*Y2/3')
    expected_A = physical.poly('X0**3*Y0**3')
    def target_matches(candidate):
        q_ast = ast.parse(candidate['q'], mode='eval').body
        return (isinstance(q_ast, ast.Constant) and type(q_ast.value) is int
                and q_ast.value == 1 and physical.poly(candidate['F']) == expected_F
                and physical.poly(candidate['A']) == expected_A)
    assert target_matches(fields) and target_matches(original)
    assert not target_matches(fields | {'q': '2'})
    assert F == expected_F == physical.poly(original['F'])
    assert A == expected_A == physical.poly(original['A'])
    assert fields['q'] == original['q'] == '1'
    def canonical_polynomial(polynomial):
        return [[list(e), c.numerator, c.denominator]
                for e, c in sorted(polynomial.items())]
    canonical_target = {'variables': list(physical.names), 'q': 1,
                        'F': canonical_polynomial(F), 'A': canonical_polynomial(A)}
    canonical_json = json.dumps(canonical_target, sort_keys=True, separators=(',', ':'))
    affine = Ring(['x', 'y', 'z', 'a', 'b'])
    substitutions = dict(zip(physical.names, [affine.const(1)] +
                         [affine.var(n) for n in ['x', 'a', 'y', 'z', 'b']]))
    affine_F = physical.subst(F, substitutions, affine)
    check('physical_endpoint_equation', affine.add(affine_F,
        affine.scale(affine.poly('a**6+b**6+(x**3*z/2+x*y/3)*a*b+'
                                '1+x**6+y**6+z**6+x*y*z/2'), -1)))
    assert physical.subst(A, substitutions, affine) == affine.poly('y**3')

    # Endpoint coordinate Jacobian det d(F,p)/d(a,b) = 6(a^6-b^6).
    p = affine.poly('a*b')
    det = affine.add(affine.mul(affine.diff(affine_F, 'a'), affine.diff(p, 'b')),
                    affine.scale(affine.mul(affine.diff(affine_F, 'b'), affine.diff(p, 'a')), -1))
    check('endpoint_coordinate_Jacobian', affine.add(det, affine.scale(affine.poly('6*(a**6-b**6)'), -1)))
    check('endpoint_curve_on_F', affine.add(affine.poly('(a**6-b**6)**2'),
        affine.scale(affine.add(affine.power(affine.add(affine_F,
                 affine.scale(affine.poly('1+x**6+y**6+z**6+x*y*z/2+'
                                          '(x**3*z/2+x*y/3)*a*b'), -1)), 2),
                 affine.scale(affine.power(p, 6), -4)), -1)))
    # -MH e0/6 = (e0+C MC e0)/(9H), cleared by 18HL.
    for i in range(4):
        check(f'source_Euler_{i}', ring.add(
            ring.scale(ring.mul(ring.var('H'), mats['H'][i][0]), -3),
            ring.scale(ring.mul(ring.var('C'), mats['C'][i][0]), -2),
            ring.scale(L, -2 if i == 0 else 0)))

    result = {
        'status': 'passed',
        'arithmetic': 'Python standard-library Fraction polynomial dictionaries',
        'connection_sha256': hashlib.sha256(args.connection.read_bytes()).hexdigest(),
        'third_kind_sha256': hashlib.sha256(args.third_kind.read_bytes()).hexdigest(),
        'target_path': str(args.target),
        'target_raw_sha256': hashlib.sha256(raw).hexdigest(),
        'original_raw_sha256': hashlib.sha256(original_raw).hexdigest(),
        'mathematical_target_unchanged': True,
        'changed_q_rejected_in_memory': True,
        'canonical_target': canonical_target,
        'canonical_target_sha256': hashlib.sha256(canonical_json.encode('utf-8')).hexdigest(),
        'canonical_target_serialization': 'UTF-8 json.dumps(canonical_target, sort_keys=True, separators=(comma,colon)), no trailing newline. Polynomials list [exponent_vector,numerator,denominator], ordered lexicographically by exponent vector; variables as listed.',
        'common_denominator': '4*H*(4*C**6-729*H**4)',
        'basis': data['basis'],
        'physical_orientation': 'Handoff source -A/6 partial_H(omega_0) uses Z=b^6-a^6 with p=ab and residue dF/F placed first. Choosing Z=a^6-b^6 changes both omega_0 and the source coefficient sign. The curve equation alone does not specify this choice.',
        'counts': {'Dwork': 8, 'Euler_matrix': 16, 'flatness': 16,
                   'third_Dwork': 2, 'third_Euler': 4, 'third_flatness': 4,
                   'third_constant_residue_audit': 1,
                   'weighted_C_gauge': 16, 'weighted_equation_discriminant': 2,
                   'physical_endpoint': 3, 'source_Euler': 4},
        'checks': checks,
        'scope': 'Exact connection and source-direction audit; no rational current, certificate, Lean proof, or acceptance.'
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
