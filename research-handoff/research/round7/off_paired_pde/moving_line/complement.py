import sympy as s
from pathlib import Path
k,t,u=s.symbols('k t tau')
Q=k**3-3*k-u;N=k*k+t*k+t*u/3;L=k**3+2*t*k*k+(3+t*u)*k+2*u
alpha=-2*t*t+8+s.Rational(5,3)*t*u;beta=3*t
R=s.Poly(s.expand((k*k-4)*L*L-alpha*N**3-beta*N**2*Q-N*Q**2),k)
co=[s.factor(c)for c in R.all_coeffs()if c]
print(co)
print('gcd',s.factor(s.gcd_list(co)))
