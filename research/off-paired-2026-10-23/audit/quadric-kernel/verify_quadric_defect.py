#!/usr/bin/env python3
"""Independent symbolic two-form transport for the actual scalar K defect.

This audits a constructive reduction, not exactness of the final form.
K is the source-bound rational function on the retained physical w cover.
"""
import json
from pathlib import Path
import sympy as s

a, b, l, h, e, i, j, c, d = s.symbols('a b l h e i j c d')
kk, kh, fw = s.symbols('K K_h f_w')
coords = (a, b, l)


def wedge(x, y):
    return {(r, t): s.cancel(x[r]*y[t]-x[t]*y[r])
            for r in range(3) for t in range(r+1, 3)}


def plus(x, y):
    return {q: s.cancel(x.get(q, 0)+y.get(q, 0)) for q in set(x)|set(y)}


def scale(z, x):
    return {q: s.cancel(z*v) for q, v in x.items()}


checks = {}
def check(name, expr):
    expr = s.cancel(expr)
    assert expr == 0, (name, expr)
    checks[name] = True


# Fixed quadric from the exact normalized canonical curve.
q = s.symbols('q')
normalized = a*a+b*b+c*q*q+d*a*q+e*q+1
quadric = a*a+b*b+i*l*l+j*a*l+l+1
check('fixed_quadric_equation', normalized.subs({c:i*e**2,d:j*e,q:l/e})-quadric)
check('physical_pencil_h', a*b/(l/e)**3-e**3*a*b/l**3)

# Full base Jacobian and weight, with h=e^-3. Relative-first orientation.
jac = s.Matrix([[e**2,0,2*i*e],[0,e,j],[0,0,1]]).det()
check('base_jacobian_dc_dd_de', jac-e**3)
check('weighted_base_volume', (-e**(-7)*e**4/(3*h)).subs(h,e**(-3))+s.Rational(1,3))

hfun = a*b/l**3
dh = [s.diff(hfun,x) for x in coords]
zeta = [s.Integer(0),s.Integer(0),b/l]
dzeta = {(0,1):0,(0,2):0,(1,2):1/l}
zdh = wedge(zeta,dh)

# R=(Z-1)K=-(h/2)K_h-K. K_h includes every derivative of the w cover.
rr = -hfun*kh/2-kk
rho = scale(-rr/3,zdh)
dcurrent = plus(scale((kk+hfun*kh)/6,wedge(dh,zeta)),
                scale(hfun*kk/6,dzeta))
defect = {(0,1):0,(0,2):-kk*b*b/(6*l**4),(1,2):0}
for pair,value in plus(rho,dcurrent).items():
    check('literal_current_pair_'+str(pair),value-defect[pair])

# Independent short proof through zeta/h=l^2 da/a's q-direction analogue.
check('zeta_divided_by_h', (b/l)/hfun-l*l/a)
twoform = plus(scale(hfun,dzeta),zdh)
for pair,value in twoform.items():
    check('d_zeta_over_h_pair_'+str(pair),value-
          ({(0,1):0,(0,2):-b*b/l**4,(1,2):0}[pair]))

# Keep the actual physical cover f(w)=1/v(i,j^2,w); eliminate only b^2.
V = i*l*l+l+1
f = s.symbols('f')
P = a**4+j*l*a**3+V*a*a+f*l**6
check('quartic_elimination',
      (a*a*quadric).subs(b*b,f*l**6/a**2)-P)
Pa = s.diff(P,a)
aw = -fw*l**6/Pa
# For d l wedge d w, d a wedge d l = -a_w d l wedge d w.
pulled = (-kk*b*b/(6*l**4)*(-aw)).subs(b*b,-a*a-j*a*l-V)
expected = kk*fw*l*l*(a*a+j*a*l+V)/(6*Pa)
check('full_quartic_source_coefficient',pulled-expected)

out = {
 'status':'Exact source-preserving rational-quadric reduction; final primitive open',
 'source':'K from actual Ssrc reduction, including its full w dependence',
 'coordinates':{'l':'e*q','h':'e^-3','c':'i*e^2','d':'j*e','Jpar':'j^2'},
 'quadric':str(quadric),
 'physical_cover':'h^2=f(w)=1/v(i,j^2,w); not discarded',
 'remainder_convention':'positive Ssrc; negate complete current for original source',
 'current_identity':'-(R/3) zeta0 wedge dh + d[(h*K/6)zeta0] = -K*b^2/(6*l^4) da wedge dl',
 'R':'-(h/2)*K_h-K',
 'zeta0':'b*dl/l',
 'quartic':str(P),
 'remaining_coefficient_dl_dw':str(expected),
 'checks':checks,'count':len(checks),
 'limitations':'Only a reduction. Rational integration on the quartic field, i,j derivatives or valid geometric serving still required.'}
path = Path(__file__).with_name('quadric-defect-results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':all(checks.values()),'output':str(path)}))
