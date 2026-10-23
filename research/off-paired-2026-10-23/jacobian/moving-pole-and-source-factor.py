"""Exact moving-pole identities and source-carrying genus-four quotient.

Research identities only: the parameter-current correction is not solved.
"""
import sympy as s
p,r,H,C=s.symbols('p r H C')
f=lambda t:(H+C*t)**2-4*t**6
t=p-r
K=-8*p**4-4*r*p**3+4*r**3*p+8*r**4
# Multiply the ds-derivative identity by Z_r Z (p-r)^2.
assert s.expand(s.diff(f(r),r)*t/2+f(r)+s.diff(f(p),p)*t/2-f(p)-K*t**2)==0
# D=partial_C-r partial_H fixes Z_r; D f(p)=2(p-r)(H+Cp).
assert s.expand(s.diff(f(p),C)-r*s.diff(f(p),H)-2*t*(H+C*p))==0
assert s.expand(s.diff(f(r),C)-r*s.diff(f(r),H))==0
print('Verified (partial_C-r partial_H) tau_r=Z_r partial_H omega_0 exactly.')
print('Verified partial_r tau_r = d_p[-Z/(Z_r(p-r))] + (8r^4 omega_0+4r^3 omega_1-4r omega_3-8omega_4)/Z_r.')

x,v,b,B=s.symbols('x v b B')
G=v**3+x**6-b*x**3-B
w=v/x
T=x**3
R=2*T+w**3-b
num=s.together(R**2-((w**3-b)**2+4*B)).as_numer_denom()[0]
assert s.rem(s.Poly(num,v),s.Poly(G,v)).is_zero
vdx=(-6*x**5+3*b*x**2)/(3*v**2)
wdx=s.diff(w,x)+s.diff(w,v)*vdx
num=s.together(-w*wdx/R-1/v).as_numer_denom()[0]
assert s.rem(s.Poly(num,v),s.Poly(G,v)).is_zero
print('Verified R^2=(w^3-b)^2+4B and dx/v=-w dw/R on v^3=-x^6+b x^3+B.')

u,V,alpha=s.symbols('u V alpha')
X=u+1/u
for sign in [1,-1]:
    Y=V*(u+sign)/u**2
    eq=s.together(Y**2-(X+2*sign)*(X**3-3*X+alpha))
    num=eq.as_numer_denom()[0]
    assert s.rem(s.Poly(num,V),s.Poly(V**2-(u**6+alpha*u**3+1),V)).is_zero
# dX/Y+ + dX/Y- = 2u du/V, exactly without using curve equation.
Yplus=V*(u+1)/u**2
Yminus=V*(u-1)/u**2
assert s.factor(s.diff(X,u)/Yplus+s.diff(X,u)/Yminus-2*u/V)==0
print('Verified both elliptic maps and source differential sum.')
print('For kappa^6=b^2+4B: dx/v=-(dX/Y_+ + dX/Y_-)/(2kappa).')
