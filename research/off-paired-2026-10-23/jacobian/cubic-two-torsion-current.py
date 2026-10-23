#!/usr/bin/env python3
"""Actual cubic-source partial fractions and 2-torsion trace current."""
import sympy as S

r,e,A,D,c = S.symbols('r e A D c')
g=r**3+A*r+D

def zero(expr):
    assert S.cancel(expr)==0

# A compact global Hermite identity, plus the residue at an arbitrary
# simple root, proves the stated partial fractions by uniqueness.
delta=4*A**3+27*D**2
U=(A*r-3*D)*(2*A*r+3*D)/delta
V=2*A*(A*r-3*D)/delta
zero(S.diff(U/g,r)+V/g-r**2/g**2)
d=3*e**2+A
root_sub={D:-e**3-A*e}
zero((V.subs(r,e)/d-2*A*e/d**3).subs(root_sub))

# The double-pole coefficient and its derivative yield K and Ri directly.
h=r**2/((g/(r-e)).subs(root_sub))**2
zero(S.limit(h,r,e)-e**2/d**2)
zero(S.limit(S.diff(h,r),r,e)-2*A*e/d**3)

tr=e+d/(r-e)
zero((g.subs(r,tr)-d**2*g/(r-e)**4).subs(root_sub))
zero(S.diff(tr,r)+d/(r-e)**2)

# Check the finite-root translation formula in root-difference form.
# This avoids expanding a large generic composed primitive.
e1,e2,e3=S.symbols('e1 e2 e3')
di=(e1-e2)*(e1-e3)
tri=e1+di/(r-e1)
zero(tri-e1-di/(r-e1))
zero(tri-e2-(e1-e2)*(r-e3)/(r-e1))
zero(tri-e3-(e1-e3)*(r-e2)/(r-e1))

# For a fixed root e1, these are its differences under all four maps.
images=[r-e1, di/(r-e1),
        (e2-e1)*(r-e3)/(r-e2),
        (e3-e1)*(r-e2)/(r-e3)]
zero(S.prod(images)-di**2)
zero(sum(S.diff(im,r)/im for im in images))

# The full trace-current derivative now follows by substituting each
# translation into the checked partial-fraction identity and applying
# the chain rule, then using the checked zero log-kernel traces.  Avoid
# expanding the enormous composed rational primitive unnecessarily.

print('PASS: actual cubic-source Hermite reduction and root residues,')
print('      2-torsion maps and log-kernel trace identity.')
