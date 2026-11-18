"""Exact resultant for the only exceptional pair of Newton faces."""
from flint import fmpz_poly
t=fmpz_poly([0,1])
left=64*6**6-(-t-3)**3*(3*t-1)*(t-1)*(-t-1)
right=(3*t-1)**3*(t-1)-4*t**2*(-t-3)*(-t-1)
res=left.resultant(right)
assert res==11734509093199349943633020232663040
print('exceptional face resultant:',res)
