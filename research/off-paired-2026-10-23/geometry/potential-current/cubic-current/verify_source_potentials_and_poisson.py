#!/usr/bin/env python3
"""Exact source potential and actual-density Poisson checks; no solve claim."""
import json
from pathlib import Path

import sympy as s

p, Hc, Bc, Cc = s.symbols("p H B C")
g = 3 * Cc * p**2 + Bc
R = Bc * p / g**3


def db(expr):
    return s.diff(expr, Bc) - p / g * s.diff(expr, p)


def zero(expr):
    return s.cancel(expr) == 0


z, U, K, t = s.symbols("z U K t")
coords = (z, U, K, t)
rho = 1 / (18 * t * z**2)
H = 1 + z**2 + t
B = U / 2 + K / 3 + z * U * K / 2
C = z**-2 + U**6 + K**6 / t
F = s.Function("F")(*coords)


def poisson(a, b):
    return 3 * z**2 * (s.diff(a, z) * s.diff(b, U)
                       - s.diff(a, U) * s.diff(b, z)) + 6 * t * (
                           s.diff(a, K) * s.diff(b, t)
                           - s.diff(a, t) * s.diff(b, K))


XF = tuple(poisson(F, q) for q in coords)
div_numerator = sum(s.diff(rho * component, q)
                    for q, component in zip(coords, XF))
coordinate_frame = (
    (0, 3 * z**2, 0, 0),
    (-3 * z**2, 0, 0, 0),
    (0, 0, 0, 6 * t),
    (0, 0, -6 * t, 0),
)

# This abstract coefficient bracket suffices for any physical H,B,C.
jhb, jhc, jbc = s.symbols("J_HB J_HC J_BC")
coefficient_coords = (Hc, Bc, Cc)
p_coefficient_derivatives = (-1 / g, -p / g, -p**3 / g)


def coefficient_gradient(a):
    return tuple(s.diff(a, q) + pq * s.diff(a, p)
                 for q, pq in zip(coefficient_coords, p_coefficient_derivatives))


def extended_bracket(a, b):
    ah, ab, ac = coefficient_gradient(a)
    bh, bb, bc = coefficient_gradient(b)
    return jhb * (ah * bb - ab * bh) + jhc * (ah * bc - ac * bh) + jbc * (ab * bc - ac * bb)


target_bracket = -p * (3 * p**2 * jhc + 2 * p**3 * jbc + jhb) / g**3
# Each summand of omega has closed coefficient times its coordinate pair.
# The only term in omega^2/2 is the product of the two displayed coefficients.
checks = {
    "implicit_second_B_derivative_is_twice_actual_R": zero(db(db(p)) - 2 * R),
    "coefficient_potential_B_derivative_is_actual_R": zero(db(-p / (2 * g)) - R),
    "symplectic_volume_is_actual_rho": zero(1 / (3 * z**2) / (6 * t) - rho),
    "general_Hamiltonian_field_preserves_actual_density": zero(div_numerator),
    "physical_H_C_bracket": zero(poisson(H, C) - 36 * (z**3 * U**5 - K**5)),
    "four_coordinate_Hamiltonians_give_stated_frame": all(
        zero(poisson(a, b) - entry)
        for a, frame_row in zip(coords, coordinate_frame)
        for b, entry in zip(coords, frame_row)),
    "extended_p_pB_bracket_retains_all_coefficients": zero(
        extended_bracket(p, -p / g) - target_bracket),
}
report = {
    "status": "exact identities only; no physical primitive or certificate",
    "checks": checks,
    "passed": sum(checks.values()),
    "total": len(checks),
}
out = Path(__file__).with_name("source-potentials-and-poisson-checks.json")
out.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
assert all(checks.values())
