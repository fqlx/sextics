"""Exact logarithmic vector fields from root motions of the elliptic cubic."""
import json
import pickle
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
L, r, x, t = sp.symbols('L r x t')
c = sp.Rational(5, 7)
variables = (L, r, x)
u = -c*c*x/4
v = x*(r-c*c/2)
w = x*(L-c*c/4)
monic = t**3+u*t**2+v*t+w
discriminant = sp.factor(sp.discriminant(monic, t)/x**2)
coordinate_jacobian = sp.Matrix([u, v, w]).jacobian(variables)
root_fields = [sp.Matrix([-3, -2*u, -v]), sp.Matrix([u, 2*v, 3*w]),
               sp.Matrix([-u*u+2*v, -u*v+3*w, -u*w])]
fields = []
for j, root_field in enumerate(root_fields):
    field = coordinate_jacobian.inv()*root_field
    if j == 0:
        field *= x  # Clear the sole coordinate denominator.
    fields.append(field.applyfunc(sp.factor))
    assert all(sp.Poly(entry, *variables, domain=sp.QQ) is not None for entry in fields[-1])
logarithmic_derivatives = []
for field in fields:
    derivative = sum(sp.diff(discriminant, z)*entry for z, entry in zip(variables, field))
    quotient, remainder = sp.div(sp.Poly(derivative, *variables), sp.Poly(discriminant, *variables))
    assert remainder.is_zero
    logarithmic_derivatives.append(sp.factor(quotient.as_expr()))
determinant_ratio = sp.factor(sp.Matrix.hstack(*fields).det()/discriminant)
assert sp.cancel(determinant_ratio/x) != 0
out = {'variables': variables, 'monic_cubic': monic, 'D': discriminant,
       'fields': fields, 'log_derivatives': logarithmic_derivatives,
       'determinant_ratio': determinant_ratio}
(HERE/'elliptic_log_fields.pickle').write_bytes(pickle.dumps(out))
report = {'variables': list(map(str, variables)),
          'D_terms': len(sp.Poly(discriminant, *variables).terms()),
          'fields': [list(map(str, field)) for field in fields],
          'log_derivatives': list(map(str, logarithmic_derivatives)),
          'determinant_ratio': str(determinant_ratio),
          'scope': 'Exact logarithmic module for the elliptic-quotient discriminant, localized at x. No current or certificate.'}
(HERE/'elliptic_log_fields.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
