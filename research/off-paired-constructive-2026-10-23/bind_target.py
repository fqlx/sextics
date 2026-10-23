"""Bind this supplement to the unchanged public off-paired F,A,q and order."""
from pathlib import Path
import re
import sympy as s

record = (Path(__file__).parent / 'live-instance.rec').read_text()
get = lambda key: re.search(r'^' + key + r': (.+)$', record, re.M).group(1)
X0,X1,X2,Y0,Y1,Y2 = s.symbols('X0 X1 X2 Y0 Y1 Y2')
variables = (X0,X1,X2,Y0,Y1,Y2)
F = sum(v**6 for v in variables) + X0**3*X1*Y0*Y1/2 + X1**3*X2*Y1*Y2/2 + X0**2*X1*X2*Y0*Y2/3
A = X0**3*Y0**3
assert int(get('q')) == 1
assert s.Poly(s.sympify(get('F')) - F, *variables).is_zero
assert s.Poly(s.sympify(get('A')) - A, *variables).is_zero
x,e,y,z,f = s.symbols('x e y z f')
affine = F.subs({X0:1,X1:x,X2:e,Y0:y,Y1:z,Y2:f})
U,W,t = x**3+y**3,x**3-y**3,x*y/z**2
H = 1+U**2-(2*t**3-1)*z**6+t*z**3/2
C = t*z**2/3+z*(U+W)/4
assert s.cancel(affine-e**6-f**6-H-C*e*f) == 0
assert A.subs({X0:1,Y0:y}) == y**3
print('PASS immutable F,A,q, variable order, and exact physical H,C source model')
