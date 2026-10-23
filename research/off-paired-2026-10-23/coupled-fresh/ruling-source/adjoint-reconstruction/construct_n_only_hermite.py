#!/usr/bin/env python3
"""Construct the rational primitive of the source-bound N-only representative.

This does not discard the original curve section: its output is the scalar K
in the retained (Z-1)K remainder.  The literal Cartan correction must be added
as specified in N-ONLY-RATIONAL-LIFT.md.  Coefficients are exact in QQ(u).
"""
from __future__ import annotations

import hashlib
import json
import time
from pathlib import Path

import sympy as s

HERE = Path(__file__).resolve().parent
DATA = HERE.parent.parent / 'genus4-gm-independent'
u, w = s.symbols('u w')
K = s.QQ.frac_field(u)
ku = K.gens[0]


def poly(expr):
    return s.Poly(expr, w, domain=K)


N = poly(9*w*w - 16*u*(1+w**3))
T = poly(1+w**3)
Nu = poly(-16*(1+w**3))
Nw = N.diff()
ONE = poly(1)
ZERO = poly(0)


def du(p):
    return s.Poly.from_dict({m: c.diff(ku) for m, c in p.rep.to_dict().items()}, w, domain=K)


def load_poly(coeffs):
    return s.Poly.from_dict({(j,): K.from_sympy(s.sympify(c)) for j, c in enumerate(coeffs)}, w, domain=K)


class RatN:
    """p(u,w)/N(u,w)^m, avoiding unnecessary rational-w gcd operations."""
    def __init__(self, p, m=0):
        self.p, self.m = p, m

    def __add__(self, other):
        if not isinstance(other, RatN):
            other = RatN(poly(other))
        m = max(self.m, other.m)
        return RatN(self.p*N**(m-self.m) + other.p*N**(m-other.m), m)

    __radd__ = __add__

    def __neg__(self):
        return RatN(-self.p, self.m)

    def __sub__(self, other):
        return self + (-other)

    def scale(self, c):
        return RatN(self.p.mul_ground(K.from_sympy(s.sympify(c))), self.m)

    def theta(self):
        return RatN((du(self.p)*N - self.p*Nu*self.m).mul_ground(ku), self.m+1)

    def shifted_theta(self, a, b=1):
        """(a+b theta) applied to this rational function."""
        return self.scale(a) + self.theta().scale(b)


def chain(r, factors):
    for a,b in factors:
        r = r.shifted_theta(a,b)
    return r


def normalise(r):
    p,m=r.p,r.m
    while m and p.rem(N).is_zero:
        p=p.exquo(N);m-=1
    return RatN(p,m)


def encode(p):
    return [str(K.to_sympy(c)) for c in reversed(p.rep.to_list())]


def integrate_poly(p):
    return s.Poly.from_dict({(j[0]+1,): c/K.convert(j[0]+1) for j,c in p.rep.to_dict().items()},w,domain=K)


def hermite(r, label):
    """Exact complete Hermite reduction, with a mandatory zero simple remainder."""
    r=normalise(r)
    p,m=r.p,r.m
    inv=s.invert(Nw,N)
    proper_terms=[]
    while m>1:
        g=(-p.rem(N)*inv).rem(N).mul_ground(K.convert(s.Rational(1,m-1)))
        proper_terms.append((m-1,g))
        # Subtract d_w(g/N^(m-1)); the resulting numerator is divisible by N.
        numerator=p-g.diff()*N+g*Nw*(m-1)
        assert numerator.rem(N).is_zero, label
        p=numerator.exquo(N)
        m-=1
        print(f'{label}: lowered denominator to N^{m}',flush=True)
    if m:
        quotient,remainder=p.div(N)
    else:
        quotient,remainder=p,ZERO
    assert remainder.is_zero, f'{label}: nonzero simple-pole remainder'
    polynomial_primitive=integrate_poly(quotient)
    # Mandatory exact verification in a common N-power denominator.
    top=max([n+1 for n,_ in proper_terms]+[0])
    check=polynomial_primitive.diff()*N**top
    for n,g in proper_terms:
        check+=(g.diff()*N-n*g*Nw)*N**(top-n-1)
    source=p if not r.m else r.p
    source=r.p*N**max(0,top-r.m)
    if top<r.m:
        check*=N**(r.m-top);source=r.p
    assert (check-source).is_zero, label
    return {
        'source_denominator_power':r.m,
        'polynomial_primitive_coefficients':encode(polynomial_primitive),
        'proper_primitive_terms':[{'denominator_power':n,'numerator_coefficients':encode(g)} for n,g in proper_terms],
        'simple_remainder_zero':True,
        'full_derivative_identity':True,
    }


def main():
    started=time.monotonic()
    source=json.loads((DATA/'corrected-rational-source-binding.json').read_text())
    potentials=json.loads((DATA/'cubic-residue-potentials-results.json').read_text())
    assert potentials['source_sha256']==source['source_sha256']
    p=potentials['actual_Ssrc_residue']
    f=load_poly(p['PE_residue_f_coefficients'])
    g=load_poly(p['PD_residue_g_coefficients'])
    crt=load_poly(p['CRT_factor_coefficients'])
    af=RatN(f*Nw,1)
    ag=RatN(g*Nw,1)
    ah=RatN(poly(54*w*(1+w**3)/u),1)
    # tLift*dlog(v)=i^-4*Pminus+i^2*Rplus, with no unlisted w-poles.
    pminus=crt*T**5*N*poly(256*(1-8*w**3))
    rplus=RatN(crt*poly(729*u*(w**9-5*w**6)))+RatN(crt*poly(729*u*w**7*(1+w**3))*Nw,1)
    # Group the exact N-only one-form by independent powers of i.
    rminus1=(chain(ah,[(2,2),(3,2)])-chain(af,[(2,2),(3,2)])
             +chain(ag,[(0,2),(1,1)])-chain(rplus,[(2,-2),(1,-2),(0,-2)]))
    rminus2=chain(af,[(1,2),(3,1)])-(ag.theta().theta().scale(4)+ag.theta().scale(-2)).scale(1/u)
    # 4u d_u^2+2d_u=(4 theta^2-2theta)/u.
    rminus7=-chain(RatN(pminus),[(-4,-2),(-5,-2),(-6,-2)])
    result={
        'source_sha256':source['source_sha256'],
        'source':'Ssrc=(D-6)(D-5)h; authoritative actual_Ssrc_residue potentials',
        'coordinates':'u=J/i^2, N=9w^2-16u(1+w^3), theta=u partial_u at fixed w',
        'N_only_remainder':'i^-1*rminus1 + i^-2*rminus2 + i^-7*rminus7',
        'certificate':False,
        'scope':'Scalar rational primitive of Cartan-reduced remainder; literal Cartan terms and the original curve-valued defect remain in full current.',
        'components':{},
    }
    for name,r in [('i^-1',rminus1),('i^-2',rminus2),('i^-7',rminus7)]:
        print(f'Beginning {name}; numerator degree {r.p.degree()}, N-power {r.m}',flush=True)
        result['components'][name]=hermite(r,name)
        (HERE/'n-only-hermite-results.json').write_text(json.dumps(result,indent=2)+'\n')
    result['elapsed_seconds']=time.monotonic()-started
    result['all_three_full_derivative_identities']=True
    (HERE/'n-only-hermite-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'elapsed_seconds':result['elapsed_seconds'],'all_three_full_derivative_identities':True,'certificate':False}),flush=True)


if __name__=='__main__':
    main()
