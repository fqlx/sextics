#!/usr/bin/env python3
"""Sparse two-component cubic gauge; all assertions are exact modulo f."""
import json
import sympy as s

H, B, C, p = s.symbols("H B C p")
f = C*p**3+B*p+H
g = 3*C*p**2+B
Delta = 4*B**3+27*C*H**2
Q = s.Matrix([B/(6*C*g), -p/(2*g)])
r = s.Matrix([-18*C*H, -2*B**2])/Delta
MH = s.Matrix([[-18*C*H, 12*B*C], [-2*B**2, -9*C*H]])/Delta
MB = s.Matrix([[27*C*H**2/B, -18*C*H], [3*H*B, -2*B**2]])/Delta
MC = -(s.eye(2)+H*MH+B*MB)/C

def zero_mod_f(expr):
    return s.rem(s.together(expr).as_numer_denom()[0], f, p) == 0

checks = {}
for variable, matrix in ((H,MH), (B,MB), (C,MC)):
    for j in range(2):
        derivative = s.diff(Q[j], variable)-s.diff(f, variable)*s.diff(Q[j],p)/g
        checks[f"connection_{variable}_{j}"] = zero_mod_f(
            derivative-sum(matrix[k,j]*Q[k] for k in range(2)))
checks["source"] = zero_mod_f(B*p/g**3-sum(r[j]*Q[j] for j in range(2)))
checks["weighted_Euler"] = all(s.cancel(x) == 0 for x in
    3*H*MH+2*B*MB-s.diag(0,-1))
checks["scaling_Euler"] = all(s.cancel(x) == 0 for x in
    H*MH+B*MB+C*MC+s.eye(2))
assert all(checks.values()), checks
print(json.dumps({"all_passed":True, "checks":checks,
    "basis":[str(q) for q in Q],
    "source":[str(s.factor(q)) for q in r],
    "MH":[[str(s.factor(x)) for x in row] for row in MH.tolist()],
    "MB":[[str(s.factor(x)) for x in row] for row in MB.tolist()],
    "MC":[[str(s.factor(x)) for x in row] for row in MC.tolist()]},indent=2))
