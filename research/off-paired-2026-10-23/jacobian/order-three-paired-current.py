#!/usr/bin/env python3
"""Exact order-three paired potential, with no density correction omitted."""
import sympy as S
x,y,k=S.symbols('x y k')
rel_y=y**2-x**3+16
rel_k=k**2+16

def zero(expr):
    num=S.together(expr).as_numer_denom()[0]
    num=S.rem(S.Poly(num,y).as_expr(),rel_y,y)
    num=S.rem(S.Poly(num,k).as_expr(),rel_k,k)
    assert S.expand(num)==0

tx=2*k*(k-y)/x**2
ty=k+64*(y-k)/x**3
mx=2*k*(k+y)/x**2
my=-k+64*(y+k)/x**3
b=lambda a:(a**3-64)/(4*a**2)
psi=lambda a:8*a/(a**3+128)
r0=lambda a:-64*a**3*(a**3-64)/(a**3+128)**3

zero(ty**2-tx**3+16)
zero(b(tx)-b(x))
zero(2*k*(k-ty)/tx**2-mx)
zero(k+64*(ty-k)/tx**3-my)
zero(psi(x)+psi(tx)+psi(mx))
zero(S.diff(psi(x),x)-r0(x)*S.diff(b(x),x))

print('PASS: constant elliptic equation, degree-three deck translation,')
print('      isogeny coordinate, trace-zero potential, exact scalar primitive.')
