#!/usr/bin/env python3
"""Exact identities for the C=0 support normalization, not a certificate."""
import json
import sympy as s

r0, r1, k, ell = s.symbols("r0 r1 k ell")
t, x, y, z = r0*k, r1*k, -s.Rational(3, 2)*r1**2*ell, r0**2*ell
H = t**6+x**6+y**6+z**6+t**3*x*y*z/2
expected = ((r0**6+r1**6)*k**6
            +(r0**12+s.Rational(729, 64)*r1**12)*ell**6
            -s.Rational(3, 4)*r0**5*r1**3*k**4*ell**2)
checks = {
    "cubic_substitution": s.expand(t*t*y+s.Rational(3, 2)*x*x*z) == 0,
    "H_substitution": s.expand(H-expected) == 0,
}
r, ss, u = s.symbols("r ss u")
A = 1+r**6
B = 1+s.Rational(729, 64)*r**12
h = A+B*ss**6-s.Rational(3, 4)*r**3*ss**2
P = 16*B*A**2-r**9
p = (64+729*u**4)*(1+u**2)**2-4*u**3
checks["eliminant_in_r_cubed"] = s.expand(4*P-p.subs(u, r**3)) == 0
checks["eliminant_squarefree"] = s.gcd(p, s.diff(p, u)) == 1
checks["eliminant_nonzero_at_zero"] = p.subs(u, 0) != 0
# On h=h_s=0: ss^2=2A/r^3 and ss^4=r^3/(4B). Substitute
# ss^6=A/(2B) into h_r before using 16BA^2=r^9.
hr_on = s.diff(A, r)+s.diff(B, r)*A/(2*B)-s.Rational(9, 2)*A/r
checks["derivative_relation_mod_eliminant"] = (
    s.factor(s.diff(P, r)-32*B*A*hr_on-9*P/r) == 0
)
checks["l_zero_simple"] = s.gcd(1+r**6, 6*r**5) == 1
checks["k_zero_simple"] = s.gcd(B, s.diff(B, r)) == 1
assert all(checks.values()), checks
print(json.dumps({"checks": checks, "all_passed": True,
                  "eliminant": str(s.expand(p))}, indent=2))
