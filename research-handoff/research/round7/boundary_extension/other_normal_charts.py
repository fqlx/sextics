"""Exact scaled implicit-function charts at q=0,infinity and 1+q^6=0."""
from pathlib import Path
import json
import sympy as s

HOME=Path(__file__).parent
q,z,j,h,H,t,T,alpha,A,v,n,e=s.symbols('q z j h H t T alpha A v n e')

def coefficients(q,h,J):
    r=h*h-4
    return [s.Rational(3,2)*J*h*r*r,
            -h*q**5/32-r*r/3888,
            h*r**3*(q**3/8-s.Rational(27,4)*J*J*h),
            h*r*r*(q**4/48+s.Rational(5,216)*J*r),
            -J*h*h*q**6/64+h*q**5*r/3456+r**3/629856]

def equations(q,h,J,alpha,t,v):
    a1,a0,b2,b1,b0=coefficients(q,h,J)
    return [b2+3*alpha**2*v**2*t+a1*alpha*v+alpha**3*v**2*(v*v+1+4*e),
            3*alpha*v*t*t+a1*t+a0*alpha*v+b1-alpha**3*v*((8*e-4)*v*v+8*e),
            t**3+a0*t+b0+4*alpha**3*(v*v+1)*((e-1)*v*v+e)]

def limit_polynomial(f,var):
    return s.cancel(f).subs(var,0).expand()

zero_raw=equations(q,q**3*H,1+q**6,alpha,T,q**3*n)
zero=[limit_polynomial(f/q**power,q) for f,power in zip(zero_raw,[6,3,0])]
infty_raw=equations(1/z,z**9*H,(1+z**6)/z**6,alpha,T,z**3*n)
infty=[limit_polynomial(f/z**power,z) for f,power in zip(infty_raw,[6,3,0])]
assert zero==infty
point={H:s.Rational(1,54),T:s.Rational(5,81),n:0}
assert all(s.cancel(f.subs(point)-target)==0 for f,target in zip(zero,[0,0,4*e*alpha**3-s.Rational(64,531441)]))
det0=s.factor(s.det(s.Matrix(zero).jacobian([H,T,alpha])).subs(point))
assert det0==s.Rational(128,3)*e*alpha**2

# At a zero of J=1+q^6, j is a local parameter.  q is a unit there.
# The independent j substitution is legitimate before imposing q^6=j-1.
jraw=equations(q,H/j**2,j,A/j**4,T/j**4,v)
jlim=[limit_polynomial(f*j**power,j) for f,power in zip(jraw,[14,13,12])]
Jpoint={H:q**3/54,T:-5*(q**3/54)**2/324,v:0}
first_two=[s.factor(f.subs(Jpoint)) for f in jlim[:2]]
assert first_two==[0,0]
detj=s.factor(s.det(s.Matrix(jlim).jacobian([H,T,A])).subs({T:-5*H**2/324,v:0}))
detj_on=s.factor(detj.subs(H,q**3/54))
assert detj_on !=0

answer={
    'base_field':'QQ(e), e^2-e+1=0',
    'q_zero':{
        'chart':'h=q^3 H, v=q^3 n; alpha,t remain finite',
        'limiting_equations':[str(f) for f in zero],
        'boundary_point':'H=1/54,t=5/81,alpha^3=16/(531441e),n=0',
        'implicit_jacobian':str(det0),
        'normal_transition':'v=q^3 n, so d/dv=q^-3 d/dn in the normal quotient',
    },
    'q_infinity':{
        'chart':'z=1/q,h=z^9 H,v=z^3 n; alpha,t remain finite',
        'limiting_equations_identical_to_q_zero':True,
        'normal_transition':'v=z^3 n, so d/dv=z^-3 d/dn in the normal quotient',
    },
    'J_zero':{
        'chart':'J=j,h=H/j^2,alpha=A/j^4,t=T/j^4; v remains finite',
        'limiting_equations':[str(f)for f in jlim],
        'implicit_jacobian_on_boundary':str(detj_on),
        'normal_transition':'v itself is a smooth normal parameter; U=J^-2 sqrt(A)',
    },
    'five_dual_forms':{
        'formula':'psi_j=e*q^(j+3)*J^2/G * U*dq tensor d/dv, j=0,...,4',
        'q_zero_order': 'j (nonnegative)',
        'q_infinity_order': '4-j (nonnegative)',
        'J_zero_order':'0: J^2 cancels the pole U~J^-2',
    },
    'scope':'These are smooth local charts on the normalization at the boundary points in question, by the displayed nonzero implicit Jacobians. P24 branch-point charts remain a separate audit; no global H10 or Gysin is asserted.'
}
(HOME/'other_normal_charts.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps(answer,indent=2))
