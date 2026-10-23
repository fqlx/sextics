"""Independent universal residue block for the rank5 moving-graph system."""
import json
import pickle
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
u, A, B, a, b = sp.symbols('u A B a b')
F = u*u+A*u+B
Delta = A*A-4*B


def reduced(expr):
    num, den = sp.fraction(sp.cancel(expr))
    assert not den.has(u)
    return sp.cancel(sp.rem(num, F, u)/den)


du = reduced(-(a*u+b)*(2*u+A)/Delta)
inverse_u = -(u+A)/B
inverse_slope = (2*u+A)/Delta
k = reduced(-sp.Rational(2, 3)*du*inverse_u-(2*du+a)*inverse_slope)
second = reduced(du+u*k)
matrix = sp.Matrix([[sp.factor(k.coeff(u, 0)), 0], [0, 0]])
# Extract polynomial coefficients after cancellation, rather than coeff on fractions.
rows = []
for expr in (k, second):
    num, den = sp.fraction(expr)
    rows.append([sp.factor(sp.Poly(num, u).coeff_monomial(u**i)/den) for i in range(2)])
matrix = sp.Matrix(rows)
assert reduced(du*(2*u+A)+a*u+b) == 0
assert sp.cancel(sp.trace(matrix)+sp.Rational(2, 3)*b/B+(2*A*a-4*b)/(2*Delta)) == 0

# Flatness in the independent universal coordinates A,B.
NA = matrix.subs({a: 1, b: 0})
NB = matrix.subs({a: 0, b: 1})
curvature = NB.diff(A)-NA.diff(B)+NB*NA-NA*NB
assert all(sp.cancel(entry) == 0 for entry in curvature)
out = {'symbols': (u, A, B, a, b), 'matrix': matrix, 'NA': NA, 'NB': NB,
       'residue_basis': ('-1/(3 W^2(2u+A))', '-u/(3 W^2(2u+A))'),
       'identity': 'u=W^3; u^2+A*u+B=0; dA=a,dB=b'}
(HERE/'residue_connection.pickle').write_bytes(pickle.dumps(out))
report = {'basis': list(out['residue_basis']), 'matrix': [[str(x) for x in row] for row in matrix.tolist()],
          'substitution': 'A=c(1+z), B=L+r*z+z^3/x; a=partial_j A,b=partial_j B',
          'trace': '-(2/3)*dB/B-(1/2)*dlog(A^2-4B)',
          'universal_flatness_exact_QQ': True,
          'scope': 'Exact independent residue quotient connection. The proper/boundary extension block and source primitive remain to be computed.'}
(HERE/'residue_connection.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
