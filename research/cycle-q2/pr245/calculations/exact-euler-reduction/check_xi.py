"""Check the second-kind toric and remaining genus-ten holomorphic transports."""
# check_kernel.L is an exact Laurent ring in I,b,T, with the on-curve J substitution.
from check_kernel import L,I,b,T,J,pt,pb,pi
from fractions import Fraction as Q
P=I**6*T**4+b**9*T**2+Q(1,2)*I*b**8*T-J*b**9*T+b**12+b**9
assert not P
assert not (-I*pi-Q(2,3)*b*pb+Q(1,6)*I*b**8*T+2*b**12+6*P)
dl=-pb*b**-3-3*T*pt*b**-4
assert dl==3*b**5-3*b**5*T**2+Q(1,2)*I*b**4*T
assert not (-I*pi*b**-4 +2*T*pt*b**-4+Q(1,6)*I*b**4*T+2*b**8+Q(2,3)*dl)
print('Both genus-ten transport coefficients of T db/b^4 and the exact rational remainder verified.')
