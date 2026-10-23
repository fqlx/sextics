"""Exact source checks for the fixed-(u,v) relative first current."""
import json
from pathlib import Path
import sympy as s

h, p, H0, C, D, u = s.symbols("h p H0 C D u")
B = u / 2 + D * h
f = H0 + h**6 + B * p + C * p**3
g = s.diff(f, p)
q = s.diff(f, h)
A = p**2 / (2 * g * q)
R = B * p / g**3

checks = {}
checks["mixed_derivatives"] = s.diff(B, h) - s.diff(q, p)
actual_p = s.diff(A, p) - (g / q) * s.diff(A, h)
checks["implicit_p_derivative"] = actual_p - B*p/(g**2*q) - 15*p**2*h**4/q**3
actual_h = s.diff(A, h) - (q / g) * s.diff(A, p)
checks["oriented_relative_source"] = -actual_h - R - 15*p**2*h**4/(g*q**2)
branch = H0 - 5*h**6 - 3*u*h**5/D - 216*C*h**15/D**3
checks["actual_remaining_pole_divisor"] = f.subs(p, -6*h**5/D) - branch

results = {name: bool(s.cancel(value) == 0) for name, value in checks.items()}
assert all(results.values()), results
out = {"status": "passed", "exact_checks": len(results), "checks": results,
       "claim": "first current plus explicit nonzero unintegrated residual; no certificate"}
path = Path(__file__).with_name("first-relative-current-checks.json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
