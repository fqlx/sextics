"""Independent exact target-to-weighted-curve source transport audit."""
import hashlib
import json
import time
from pathlib import Path
import sympy as sp
import yaml

HERE = Path(__file__).resolve().parent
started = time.monotonic()
target = Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec')
record = yaml.safe_load(target.read_text())
X0, X1, X2, Y0, Y1, Y2 = sp.symbols('X0 X1 X2 Y0 Y1 Y2')
h, W, y, a, b, v, t = sp.symbols('h W y a b v t')
coordinates = [h, v*h, W, a*y, b*y, y]
old_variables = [X0, X1, X2, Y0, Y1, Y2]
substitution = dict(zip(old_variables, coordinates))
F = sp.sympify(record['F'])
A = sp.sympify(record['A'])
assert A == X0**3*Y0**3
expanded = sp.Poly(sp.expand(F.subs(substitution)), y)
assert all(exponent[0] % 2 == 0 for exponent, _ in expanded.terms())
curve = sum(coefficient*t**(exponent[0]//2)
            for exponent, coefficient in expanded.terms())
c = sp.Rational(5, 7)
Bp, Pp, Qp, Rp, Sp = [b*(1+a*v), 1+v**6, c*a*b*v,
                       c*(a*b+v*b**3), 1+a**6+b**6]
expected = (W**6+c*(h**3+Bp*h*t)*W**3+Pp*h**6
            +Qp*h**4*t+Rp*h**2*t**2+Sp*t**3)
assert sp.expand(curve-expected) == 0
jacobian = sp.Matrix(coordinates).jacobian([h, W, y, a, b, v]).det()
assert sp.expand(jacobian-h*y**2) == 0
# dy=dt/(2y); the original Euler field becomes h d_h+W d_W+2t d_t.
coefficient = sp.cancel(A.subs(substitution)*jacobian/(2*y))
assert sp.expand(coefficient-a**3*h**4*y**4/2) == 0

# Verify the curve normalization universally, before inserting the base map.
B, P, Q, R, S, T = sp.symbols('B P Q R S T')
beta = -R/(3*S)
M = 1+B*beta
alpha = M/B
L = (P+Q*beta+R*beta**2+S*beta**3)/M**2
r = (Q-R**2/(3*S))/(B*M)
x = B**3/(S*M)
old_t = alpha*T+beta*h**2
transformed = (M**2*W**6+c*(h**3+B*h*old_t)*M*W**3
               +P*h**6+Q*h**4*old_t+R*h**2*old_t**2+S*old_t**3)
canonical = W**6+c*(h**3+h*T)*W**3+L*h**6+r*h**4*T+T**3/x
assert sp.cancel(transformed-M**2*canonical) == 0
# W_old=rho*W, rho^3=M; the fiber Jacobian is rho*alpha.
assert sp.cancel(alpha/M**4-1/(B*M**3)) == 0
report = {
    'target_id': record['id'], 'raw_instance_rec_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    'target_polynomial_pullback_verified': True,
    'affine_jacobian': str(jacobian),
    'source_on_weighted_curve': 'a^3*h^4*t^2/2 times Omega/C^2 wedge da db dv',
    'weighted_euler_weights': [1, 1, 2],
    'universal_canonical_curve_transform_verified': True,
    'canonical_source': 'rho*a^3/(2*B*M^3) * h^4*(alpha*T+beta*h^2)^2 times Omega/Ccanonical^2 wedge da db dv',
    'character': 'rho^3=M; rational currents after extracting this character retain (1/3)dlog(M)',
    'seconds': time.monotonic()-started,
    'scope': 'Exact source and coordinate transport only; no rational primitive or protected certificate.'
}
(HERE/'independent_physical_source.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
