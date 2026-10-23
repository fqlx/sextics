"""Exact QQ audit of the conductor's transverse normalization.

This intentionally recomputes the second implicit jet over QQ[q]/(G),
rather than inferring it from finite-field data.
"""
from pathlib import Path
import json, pickle, time
import sympy as sp
from flint import fmpq, fmpq_poly

HOME = Path(__file__).parent
START = time.time()
q, h, ell = sp.symbols('q h ell')
model = pickle.loads(Path('/workspace/research/round7/moving_j1728/physical_model.pickle').read_bytes())
coeff = {name: value.subs({model['symbols']['q']: q, model['symbols']['h']: h})
         for name, value in model['coefficients'].items()}
J = 1 + q**6
G = 46656*q**24 + 19683*q**22 + 186624*q**18 + 59049*q**16 + 279936*q**12 + 59049*q**10 + 186620*q**6 + 19683*q**4 + 46656
normal = json.loads(Path('/workspace/research/round7/off_paired_pde/moving_line/j0_boundary_normal.json').read_text())
R1 = sp.sympify(normal['R1'], locals={'q': q, 'ell': ell})

def poly(expression):
    p = sp.Poly(expression, q)
    return fmpq_poly([fmpq(str(p.nth(i))) for i in range(p.degree()+1)])

g = poly(G)
g /= g.leading_coefficient()
x = fmpq_poly([0, 1])
one = fmpq_poly([1])

def inv(a):
    gcd, u, _ = a.xgcd(g)
    assert gcd.degree() == 0
    return u / gcd[0] % g

def mul(a, b):
    return a*b % g

hh = mul(x**3, inv(54*mul(one+x**6, one+x**6)))

def evaluate_polynomial(expression):
    answer = fmpq_poly([])
    for (aq, ah), c in sp.Poly(expression, q, h).terms():
        answer += mul(x**aq % g, hh**ah % g) * fmpq(str(c))
    return answer % g

def evaluate(expression):
    num, den = sp.fraction(sp.cancel(expression))
    return mul(evaluate_polynomial(num), inv(evaluate_polynomial(den)))

names = ['a1', 'a0', 'b2', 'b1', 'b0']
c0, c1, c2 = [{name: evaluate(sp.diff(coeff[name], h, order)) for name in names}
              for order in range(3)]
a1, a0, b2, b1, b0 = [c0[name] for name in names]
assert not b2
t0 = mul(-b1, inv(a1))

# z=alpha*v.  Mod alpha^3 the first two slope equations are exactly
# b2(h)+a1(h)z+3t*z^2=0 and a1(h)t+b1(h)+(3t^2+a0(h))*z=0.
# Write h=h0+H1*z+H2*z^2 and t=t0+T1*z+T2*z^2.
H1 = mul(-a1, inv(c1['b2']))
T1 = mul(-(mul(c1['a1'], t0)+c1['b1'])*H1 % g -3*mul(t0,t0)-a0, inv(a1))
H2 = mul(-(mul(c2['b2'], mul(H1,H1))/2 + mul(c1['a1'],H1)+3*t0), inv(c1['b2']))
T2 = mul(-(mul(mul(c1['a1'],t0)+c1['b1'],H2)
           +mul(mul(c2['a1'],t0)+c2['b1'],mul(H1,H1))/2
           +mul(mul(c1['a1'],H1),T1)+6*mul(t0,T1)+mul(c1['a0'],H1)), inv(a1))

# Coefficient of z^2 in Fbar=t^3+a0(h)t+b0(h).
C = (mul(mul(c1['a0'],t0)+c1['b0'],H2)
     +mul(3*mul(t0,t0)+a0,T2)
     +mul(mul(c2['a0'],t0)+c2['b0'],mul(H1,H1))/2
     +mul(mul(c1['a0'],H1),T1)+3*mul(t0,mul(T1,T1))) % g
Gp = poly(sp.diff(G,q))
rr = (mul(hh,hh)-4) % g
A = 4*mul(rr, mul(mul(Gp,inv(poly(17006112*J**4))),
                    mul(Gp,inv(poly(17006112*J**4))))) % g
LoverG = sp.cancel(-4*ell*R1/G)
assert not LoverG.has(ell)
B = mul(Gp, evaluate(LoverG))
discriminant = (4*mul(A,C)-mul(B,B)) % g
assert not discriminant
assert A.gcd(g).degree() == 0

answer = {
    'base_field': 'QQ',
    'conductor_degree': g.degree(),
    '4AC_minus_B_squared_is_zero_mod_G': not discriminant,
    'quadratic_q_coefficient_is_a_unit_mod_G': A.gcd(g).degree() == 0,
    'normalization': 'Two smooth formal sheets in coordinates (U,v); v has normal order zero.',
    'reason': 'Eliminate h,t. Up to alpha^2, F(q,alpha,v)=Fbar(q,alpha*v). The exact vanishing Hessian discriminant makes the critical value O(alpha^3). With alpha=U^2 the formal Morse lemma factors F into q-Q(U^2,v)=+-U^3 times a unit.',
    'scope': 'Only conductor G=0, away from q=0, P=0 and infinity. Does not prove the global normal bundle, global H10, or Gysin binding.',
    'elapsed_seconds': round(time.time()-START,3),
}
(HOME/'conductor_normalization.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps(answer,indent=2))
