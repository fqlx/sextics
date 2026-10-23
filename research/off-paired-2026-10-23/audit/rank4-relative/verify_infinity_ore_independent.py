"""Separate exact Ore-algebra audit of the infinity compact-source match.

This verifies operators, not the missing horizontal residue primitive.
"""
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
H, C = s.symbols("H C")
data = json.loads((ROOT / "coupled-fresh/rank4-relative/infinity-ore-general.json").read_text())
parse = lambda key: [s.sympify(v, locals={"H": H, "C": C}) for v in data[key]]
U, V, M = (parse(key) for key in ("U", "V", "M"))
Delta = 4*C**6 - 729*H**4
L = [55*C**2/Delta, 309*C**3/Delta,
     (271*C**6-1458*H**4)/(C**2*Delta),
     2*(32*C**6+729*H**4)/(C*Delta), s.Integer(1)]

def compose(left, right):
    ans = [s.Integer(0)]*(len(left)+len(right)-1)
    for i, ai in enumerate(left):
        for j, bj in enumerate(right):
            for k in range(i+1):
                ans[j+k] += ai*s.binomial(i,k)*s.diff(bj,C,i-k)
    return [s.cancel(v) for v in ans]

def adjoint(op):
    ans = [s.Integer(0)]*len(op)
    for i, ai in enumerate(op):
        for k in range(i+1):
            ans[k] += (-1)**i*s.binomial(i,k)*s.diff(ai,C,i-k)
    return [s.cancel(v) for v in ans]

def add(left, right):
    n = max(len(left),len(right))
    return [s.cancel((left[i] if i<len(left) else 0)+(right[i] if i<len(right) else 0)) for i in range(n)]

count = 0
one = add(compose(U,L),compose(V,M))
assert one == [s.Integer(1)]+[s.Integer(0)]*(len(one)-1)
count += 1
Ls, Us, Vs, Ms = map(adjoint,(L,U,V,M))
one_adj = add(compose(Ls,Us),compose(Ms,Vs))
assert one_adj == [s.Integer(1)]+[s.Integer(0)]*(len(one_adj)-1)
count += 1
for op in (L,U,V,M):
    assert all(s.cancel(a-b)==0 for a,b in zip(adjoint(adjoint(op)),op))
    count += 1

# The actual DH/DC commute on the physical field. Thus the coefficient of
# D_C^j in [T,V*] is T(v_j*)-2j v_j*/(3H).
for j, coefficient in enumerate(Vs):
    comm = s.diff(coefficient,H)+2*C*s.diff(coefficient,C)/(3*H)-2*j*coefficient/(3*H)
    assert s.cancel(comm)==0
    count += 1

# Literal compact source identity on an arbitrary physical coefficient.
# The composition identity is stronger than individual substitutions, but
# these choices independently exercise nonconstant source derivatives.
for sigma in (C**3/H, C**-1/H**2, C**2*H):
    apply = lambda op,f: s.cancel(sum(a*s.diff(f,C,j) for j,a in enumerate(op)))
    f = -apply(Us,sigma)
    xi = apply(Vs,sigma)
    assert s.cancel(-apply(Ls,f)+apply(Ms,xi)-sigma)==0
    count += 1

out = {"exact_check_groups": count, "status": "passed",
       "scope": "Ore source matching and T-commutation only; horizontal residue curl remains unsolved"}
(Path(__file__).with_suffix(".json")).write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
