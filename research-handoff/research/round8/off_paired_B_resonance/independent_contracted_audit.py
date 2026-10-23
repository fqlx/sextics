"""Replay the candidate obstruction directly in the cleared p equation.

This deliberately bypasses the compact charge and A0/C0 formulas.
It checks the nu^3 coefficients for p=nu^2*f(V)/(s*q0) in the actual
contracted boundary operator, with formal independent jets of f.
"""
import json
import time
from pathlib import Path
import sympy as sp
from flint import fmpq_mpoly, fmpq_mpoly_ctx

HERE = Path(__file__).resolve().parent
started = time.monotonic()
eta, V, s = sp.symbols('eta V s')
nu = 9*eta+14
eta0 = -sp.Rational(14, 9)
obj = json.loads(Path('/workspace/research/round8/cyclic_companion/gist/results/original_scalar_input.json').read_text())
data = obj['contracted_boundary_reduction']
ctx = fmpq_mpoly_ctx.get(('eta', 'V', 's'))


def boundary(text):
    poly = fmpq_mpoly(text.replace('**', '^'), ctx)
    return sum(sp.Rational(str(c))*eta**e[0]*V**e[1]
               for e, c in poly.to_dict().items() if e[2] == 0)


Y = [sp.sympify(text) for text in data['Y_components']]
Y0, Y1 = [sp.factor(f.subs(s, 0)) for f in Y[:2]]
Ys = sp.factor(sp.diff(Y[2], s).subs(s, 0))
assert Y[2].subs(s, 0) == 0
D0 = sp.factor(3*(1+V**6)*boundary(data['Delta0']))
BC = [boundary(data[name]) for name in ('Bred', 'Cred')]
q0 = 3*(1+V**6)


def tangent(f):
    return Y0*sp.diff(f, eta)+Y1*sp.diff(f, V)


z = nu**2/q0
A = sp.cancel(tangent(z)-Ys*z)
B = z*Y1
print('BOUNDARY_LOADED', time.monotonic()-started, flush=True)
raw = [D0*(tangent(A)-Ys*A)+BC[0]*A+BC[1]*z,
       D0*(A*Y1+tangent(B)-Ys*B)+BC[0]*B,
       D0*B*Y1]


def coefficient_nu3(f):
    num, den = sp.fraction(sp.cancel(f))
    assert den.subs(eta, eta0) != 0
    # All three lower coefficients must vanish in the exact cleared equation.
    for order in range(3):
        assert sp.cancel(sp.diff(num, eta, order).subs(eta, eta0)) == 0
    return sp.factor(sp.diff(num, eta, 3).subs(eta, eta0)/(sp.factorial(3)*9**3*den.subs(eta, eta0)))


actual = [coefficient_nu3(f) for f in raw]
rhs = coefficient_nu3(boundary(data['rhsred']))
C = -sp.Rational(475, 3)*V**2/(14*V**2+9)
r = (V**6-1)/(V*(1+V**6))
# T4 = C*d/dV - 4*C*r; square on independent formal jets.
a = -4*C*r
expected = [C*sp.diff(a, V)+a*a,
            C*sp.diff(C, V)+2*a*C,
            C*C]
Dlead = sp.cancel(D0/nu).subs(eta, eta0)
factor = sp.factor(Dlead**3/q0)
for actual_coefficient, expected_coefficient in zip(actual, expected):
    assert sp.cancel(actual_coefficient-factor*expected_coefficient) == 0
R0 = sp.Rational(4500846, 125)*(28*V**6+9*V**4+14)/(V*(14*V**2+9)**3)
assert sp.cancel(rhs-factor*R0) == 0
report = {
    'field': 'QQ(V)',
    'cleared_operator_nu3_formal_jet_coefficients_match_T4_squared': True,
    'cleared_rhs_nu3_matches_R0': True,
    'all_lower_nu_coefficients_zero': True,
    'method': 'Direct contracted Bred/Cred and rhsred replay; no compact charge or A0/C0 used.',
    'seconds': time.monotonic()-started,
    'scope': 'Audit of the generic scalar-route obstruction. Not an unrestricted sextic-certificate obstruction.'
}
(HERE/'independent_contracted_audit.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2), flush=True)
