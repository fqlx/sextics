#!/usr/bin/env python3
"""Exact density and complete CM connection interface for the actual Pa residue.

This is a coordinate/current audit. It does not assert a primitive of the
remaining compact genus-four source.
"""
import json
from pathlib import Path
import sympy as s

i, u, w, h, t, A, B, K = s.symbols('i u w h t A B K')
T = 1+w**3
N = 9*w*w-16*u*T
aa = 36*T**3/(u*w)
bb = 6561*w**5/(64*N*T**2)
v = 64*u*w*N*T**2/(9*(256*T**5*N+729*i**6*u*w**6))
checks = {}


def check(name, expr):
    assert s.cancel(expr) == 0, (name, s.cancel(expr))
    checks[name] = True


check('actual physical inverse root has sextic CM form', 1/v-aa-bb*i**6)
fi = s.diff(aa+bb*i**6, i)
fu = s.diff(aa+bb*i**6, u)
fw = s.diff(aa+bb*i**6, w)
# j=i*t, t²=u. The h_i and h_u entries are included, not omitted.
jac = s.Matrix([[1,0,0],[t,i/(2*t),0],[fi/(2*h),fu/(2*h),fw/(2*h)]]).det()
check('full Pa residue volume with transverse derivatives', jac-i*fw/(4*t*h))


def reduced(expr):
    numerator = s.fraction(s.cancel(expr))[0]
    return s.Poly(numerator,h).rem(s.Poly(h*h-A-B*i**6,h)).as_expr()


def di(expr):
    return s.diff(expr,i)+3*B*i**5*s.diff(expr,h)/h


def da(expr):
    return s.diff(expr,A)+s.diff(expr,h)/(2*h)


def db(expr):
    return s.diff(expr,B)+i**6*s.diff(expr,h)/(2*h)


# All four compact classes, plus both relevant residue classes, are retained.
for n in (-1,0,1,2,3,4):
    omega = i**n/h
    fa = -i**(n+1)/(6*A*h)
    fb = i**(n+1)/(6*B*h)
    check('CM A connection n='+str(n),
          reduced(da(omega)-(n-2)*omega/(6*A)-di(fa)))
    check('CM B connection n='+str(n),
          reduced(db(omega)+(n+1)*omega/(6*B)-di(fb)))

# Deterministic monomial reductions, including the second-kind powers.
for n in (3,4,5,6,7,8,9,10,11):
    if n == 2:
        continue
    check('descending exact monomial recurrence n='+str(n),
          reduced(i**n/h-di(i**(n-5)*h)/((n-2)*B)
                  +(n-5)*A*i**(n-6)/((n-2)*B*h)))
for n in (-8,-7,-6,-5,-4,-3,-2):
    check('ascending exact monomial recurrence n='+str(n),
          reduced(i**n/h-di(i**(n+1)*h)/((n+1)*A)
                  +(n+4)*B*i**(n+6)/((n+1)*A*h)))

result = {
 'status':'Exact actual-source Pa density and complete isotrivial CM connection interface',
 'physical_cover':'h²=1/v=A(u,w)+B(u,w)*i^6; retained',
 'A':str(s.factor(aa)), 'B':str(s.factor(bb)),
 'coordinates':'u=J/i², j=i*sqrt(u), h=e^-3',
 'full_density_K_di_dj_dh':str(i*K*fw/(4*t*h)),
 'density_orientation':'di wedge du wedge dw; t²=u',
 'actual_Pa_residue':'±sqrt(-1)/6 times K di wedge dj wedge dh',
 'compact_basis_indices':[0,1,3,4],
 'additional_residue_indices':[-1,2],
 'connection':'nabla omega_n=((n-2)dlogA-(n+1)dlogB)/6*omega_n + d_i[i^(n+1)/(6h)*(dlogB-dlogA)]',
 'omega_n':'i^n di/h',
 'scope':'The physical K remains source-bound. Full-base Pa primitive can be extracted from existing Green currents; a pure-w primitive is not assumed. Compact genus-four serving remains open.',
 'checks':checks,'count':len(checks)
}
out=Path(__file__).with_name('isotrivial-pa-interface-results.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'pass':True,'count':len(checks),'output':str(out)}))
