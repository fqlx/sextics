#!/usr/bin/env python3
"""Exact source/normal identities for the cubic-ray elliptic companion.

This checks identities only.  It does not construct a source primitive.
"""
import sympy as S

x, a, u, v, y, s, w = S.symbols('x a u v y s w')
H, B, C = S.symbols('H B C', nonzero=True)
f = H + B*s + C*s**3
fp = S.diff(f, s)
E = w**2 - f

def zero(expr):
    assert S.cancel(expr) == 0

Hphys = 1 + x**6 + a**6
Cphys = 1 + u**6 + v**6
Bphys = x*u/2 + x**3*a*u*v/2 + x*a*v/3
Fphys = (1+x**6+a**6+y**6+(y*u)**6+(y*v)**6
         + x*y*(y*u)/2 + x**3*a*(y*u)*(y*v)/2
         + x*a*y*(y*v)/3)
zero(Fphys - f.subs({H:Hphys, B:Bphys, C:Cphys, s:y**2}))

# d(Y0,Y1,Y2)/d(y,u,v)=y^2, so y^3 times this determinant
# times dy/ds is s^2/2 after s=y^2.
J = S.Matrix([y,y*u,y*v]).jacobian([y,u,v]).det()
zero(J-y**2)
zero(y**3*J/(2*y) - y**4/2)

source = s**2/(2*f**2)
vertical = -S.diff(1/f, s)/(6*C)
remaining = -B/(6*C*f**2)
zero(source-vertical-remaining)

# Full Hermite first current with discriminant denominator only.
delta = 4*B**3+27*H**2*C
Q = (B*s-3*H)*(2*B*s+3*H)/(2*delta)
simple = B*(B*s-3*H)/delta
zero(source-S.diff(Q/f,s)-simple/f)
zero((delta-fp**2*(4*B+3*C*s**2)).subs(H,-B*s-C*s**3))
zero((simple-B*s/fp**2).subs(H,-B*s-C*s**3))

# The actual second normal residue in the f-normal coordinate.
# If P=s^2/2, its density is (1/f_s) d_s(P/f_s).
R = S.diff((s**2/2)/fp,s)/fp
zero(R-B*s/fp**3)
sH = -1/fp
sHH = S.diff(sH,s)*sH
zero(R + B*sHH/(6*C))

# On E=w^2-f=0, the w-normal residue of b/E^2 is
# b_w/(4w^2)-b/(4w^3).  The actual numerator is rational.
def second_normal(b):
    return S.diff(b,w)/(4*w**2)-b/(4*w**3)

b = -s**2/w
zero(second_normal(b)-s**2/(2*w**4))
b_reduced = B/(3*C*w)
zero(second_normal(b_reduced)+B/(6*C*w**4))

# Replacing 1/w by w/f makes the second residue zero.  The
# equation-multiple correction is exactly the original source again.
b_tilde = -s**2*w/f
zero(second_normal(b_tilde))
zero(b-b_tilde - s**2*E/(w*f))
first_correction = (s**2/(w*f))/(2*w)
zero(first_correction.subs(w**2,f)-source)

# Rescaling r=C*s, W=C*w gives the stated Weierstrass equation.
r, W = S.symbols('r W')
zero((W**2-r**3-B*C*r-H*C**2).subs({r:C*s,W:C*w})-C**2*E)
j = S.cancel(1728*4*(B*C)**3/(4*(B*C)**3+27*(H*C**2)**2))
zero(j-6912*B**3/(4*B**3+27*H**2*C))

# Full-kernel mu_6 quotient a->zeta*a, v->zeta^-1*v.
k,t = S.symbols('k t', nonzero=True)
Jquot = S.Matrix([x,u,a*v,a**6]).jacobian([x,a,u,v]).det()
zero(Jquot-6*a**6)
Hquot = 1+x**6+t
Cquot = 1+u**6+k**6/t
Bquot = x*u/2+x**3*u*k/2+x*k/3
Gquot = t**2+(1+x**6+Bquot*s+(1+u**6)*s**3)*t+k**6*s**3
zero(t*f.subs({H:Hquot,C:Cquot,B:Bquot})-Gquot)
zero((s**2/(2*f**2)).subs({H:Hquot,C:Cquot,B:Bquot})/(6*t)
     -t*s**2/(12*Gquot**2))

print('PASS: physical chart, vertical reduction, actual normal residue,')
print('      discriminant Hermite current, rational companion numerator,')
print('      correction self-cycle, j, and full-kernel mu_6 quotient.')
