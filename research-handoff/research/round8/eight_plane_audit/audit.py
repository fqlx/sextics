"""Independent exact audit of the eight-plane quartic source packet.

This checks identities, not existence of the final rational current.
"""
from pathlib import Path
import json
import pickle
import sympy as s

HERE = Path(__file__).parent
PACKET = HERE.parent / "eight_plane_quartic"
model = pickle.loads((PACKET / "model.pickle").read_bytes())
herm = pickle.loads((PACKET / "hermite.pickle").read_bytes())
source = pickle.loads((PACKET / "source.pickle").read_bytes())
checks = {}

# Compute the projective Euler contraction directly, rather than recovering
# it from the full six-variable chart Jacobian used by model.py.
z, u, v, r, t = s.symbols("z u v r t")
U, V = [z, z*u, z*v], [1, r, t]
xx = [(a+b)/2 for a, b in zip(U, V)]
yy = [(a-b)/(2*s.I) for a, b in zip(U, V)]
coords = s.Matrix(xx + yy)
minor = s.Matrix.hstack(coords, coords.jacobian([z, u, v, r, t]))
omega = s.factor(minor.det())
assert omega == s.I*z*z/8
A = s.factor(xx[0]**3 * yy[0]**3)
assert s.expand(A-s.I*(z*z-1)**3/64) == 0
assert s.cancel(A*omega/(z*z) + (z*z-1)**3/512) == 0
checks["direct_projective_minor"] = str(omega)
checks["direct_source_factor"] = "-1/512"
print("direct source checked", flush=True)

# Exact polynomial identity and exact denominators of the saved universal
# Hermite solution.  In particular B has no leading-coefficient pole.
zz, g = herm["z"], herm["g"]
G, N, disc = herm["G"], herm["N"], herm["Delta"]
P = sum(c*zz**i for i, c in enumerate(herm["P_coefficients"]))
B = sum(c*zz**i for i, c in enumerate(herm["B_coefficients"]))
assert s.cancel(s.diff(P, zz)*G - P*s.diff(G, zz) + B*G - N) == 0
assert s.factor(herm["hermite_matrix"].det() - g[4]*disc) == 0
for c in herm["P_coefficients"]:
    assert s.factor(s.denom(c)/(g[4]*disc)) in (1, -1)
for c in herm["B_coefficients"]:
    assert s.factor(s.denom(c)/disc) in (1, -1)
checks["hermite_identity"] = True
checks["hermite_determinant"] = "g4*Disc(G)"
checks["P_denominator"] = "g4*Disc(G)"
checks["B_denominator"] = "Disc(G)"
print("Hermite and denominators checked", flush=True)

# The double-pole residue computed from local Taylor expansion agrees with
# the simple-pole representative B/G'.  Clear denominators and reduce only
# after differentiating, so no root branches are chosen.
Gp, Gpp, Np = s.diff(G, zz), s.diff(G, zz, 2), s.diff(N, zz)
local_difference = s.cancel(B*Gp**2 - Np*Gp + N*Gpp)
local_num = s.fraction(local_difference)[0]
assert s.rem(local_num, G, zz) == 0
checks["local_double_pole_residue"] = "(N'*G'-N*G'')/(G')^3 = B/G' mod G"
print("local residue checked", flush=True)

# Lagrange interpolation proves Tr(z^j/G')=0 for j<3: compare the z^3
# coefficient in the degree<=3 interpolation of z^j at four distinct roots.
# Verify those coefficient identities after multiplying by a Vandermonde,
# avoiding a second expansion of the large saved rho power coefficients.
ts = s.symbols("t0:4")
vand = s.prod(ts[j]-ts[i] for i in range(4) for j in range(i+1,4))
for power in range(3):
    total = 0
    for i in range(4):
        di = s.prod(ts[i]-ts[j] for j in range(4) if j != i)
        total += ts[i]**power*s.cancel(vand/di)
    assert s.expand(total) == 0
assert s.degree(B, zz) <= 2
checks["Lagrange_trace_zero"] = True
print("trace checked", flush=True)

# Verify Ferrari over independently labeled roots.  The common flag is an
# ordered choice of a root together with an unordered pair containing it.
a, b, c = s.symbols("a b c")
roots = [a, b, c, -a-b-c]
p = sum(roots[i]*roots[j] for i in range(4) for j in range(i+1, 4))
q = -sum(roots[i]*roots[j]*roots[k]
         for i in range(4) for j in range(i+1, 4) for k in range(j+1, 4))
rr = s.prod(roots)
c1, c2, c3 = s.symbols("c1 c2 c3")
c0 = (2*p*c2 + 3*q*c3)/4
residue = lambda x: c0+c1*x+c2*x*x+c3*x**3
anti = lambda y: c1-q*c2/y-(y+3*p)*c3/2
for i in range(4):
    recovered = 0
    for j in range(4):
        if i == j:
            continue
        w = roots[i]+roots[j]
        y = w*w
        assert s.cancel(residue(roots[i])+residue(roots[j])-w*anti(y)) == 0
        assert s.expand(y**3+2*p*y*y+(p*p-4*rr)*y-q*q) == 0
        recovered += w*anti(y)/2
    assert s.cancel(recovered-residue(roots[i])) == 0
checks["Ferrari_pair_trace"] = True
checks["Ferrari_inverse_half_trace"] = True
checks["Ferrari_preserves_standard_sector"] = True
print("Ferrari checked", flush=True)

# Audit the derivative convention directly in the cubic algebra, using a
# separate formula for y_i and differentiating all three basis elements.
par = source["resolvent_symbols"]
pp, qq, rr, y = (par[n] for n in ("p", "q", "r", "y"))
res = source["resolvent"]
F = s.QQ.frac_field(pp, qq, rr)
RR = s.Poly(res, y, domain=F)
def rem(expr):
    return s.Poly(expr, y, domain=F).rem(RR).as_expr()
inverse_prime = s.invert(s.diff(res, y), res, y)
inverse_y = s.invert(y, res, y)
for name, parameter in (("p", pp), ("q", qq), ("r", rr)):
    dy = rem(-s.diff(res, parameter)*inverse_prime)
    mat = source["charged_connections"][name]
    for j in range(3):
        expected = rem(s.Rational(2*j+1, 2)*dy*
                       (y**(j-1) if j else inverse_y))
        assert s.cancel(expected-sum(mat[i,j]*y**i for i in range(3))) == 0
for n1, x1 in (("p", pp), ("q", qq), ("r", rr)):
    for n2, x2 in (("p", pp), ("q", qq), ("r", rr)):
        if n1 >= n2:
            continue
        M1 = source["charged_connections"][n1]
        M2 = source["charged_connections"][n2]
        curvature = M2.diff(x1)-M1.diff(x2)+M1*M2-M2*M1
        assert all(s.cancel(x) == 0 for x in curvature)
checks["charged_connection_columns"] = True
checks["charged_connection_flatness"] = True

report = {
    "checks": checks,
    "scope": "Exact identity and transfer audit only; no rational current, serving support, or certificate obtained.",
    "remaining_equation": "sum_i (partial_i + y_i/(2*y))*u_i = -f(y)/512 on the actual four-variable physical base",
}
(HERE / "audit.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2), flush=True)
