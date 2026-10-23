"""Exact source, normal residue, and conditional current transport audit.

This does not search for, or claim, a primitive.
"""
import hashlib
import json
from pathlib import Path
import sympy as S

checks = []

def check(name, expression):
    assert S.cancel(expression) == 0, name
    checks.append(name)

x, a, y, Y1, Y2, s, u, v = S.symbols('x a y Y1 Y2 s u v')
q = (x, a, u, v)
H = 1+x**6+a**6
B = x*u/2+x**3*a*u*v/2+x*a*v/3
C = 1+u**6+v**6
f = H+B*s+C*s**3
physical = (x, a, y, Y1, Y2)
theta = S.Matrix((x, a, y**2, Y1/y, Y2/y))
pull = {s:y**2, u:Y1/y, v:Y2/y}
F = 1+x**6+a**6+y**6+Y1**6+Y2**6+x*y*Y1/2+x**3*a*Y1*Y2/2+x*a*y*Y2/3
check('immutable_affine_F', f.subs(pull)-F)
Jac = theta.jacobian(physical)
check('quotient_jacobian', Jac.det()-2/y)
A0 = s**2/2
check('actual_source_density', A0.subs(pull)*Jac.det()-y**3)
g = S.diff(f,s)
R = B*s/g**3
check('normal_residue', S.diff(A0/g,s)/g-R)
check('coefficient_H_second_derivative', -B/(6*C)*(-6*C*s/g**3)-R)

# The normal Jacobian derivative is necessary for every base direction.
for qi in q:
    fq = S.diff(f,qi)
    Di_g = S.diff(g,qi)-fq*S.diff(g,s)/g
    check('normal_jacobian_'+str(qi), S.diff(fq/g,s)-Di_g/g)

# Piola identity for arbitrary vector values and arbitrary first jets.
Vs = S.symbols('Vx Va Vs Vu Vv')
jets = S.Matrix(5,5,lambda i,j:S.Symbol('dV'+str(i)+str(j)))
J = 2/y
P = J*Jac.inv()
W = P*S.Matrix(Vs)
for j in range(5):
    check('normal_pairing_'+str(j), sum(S.diff(F,physical[i])*P[i,j] for i in range(5))-J*S.diff(f,(x,a,s,u,v)[j]).subs(pull))
div_pull = 0
for i in range(5):
    div_pull += S.diff(P[i,:].dot(S.Matrix(Vs)),physical[i])
    for j in range(5):
        for k in range(5):
            div_pull += P[i,j]*jets[j,k]*Jac[k,i]
check('piola_full_first_jet', div_pull-J*S.trace(jets))

# Conditional ambient lift, checked by comparing its independent a_i jets.
ai = S.symbols('ax aa au av')
ais = S.symbols('axs aas aus avs')
aiq = S.Matrix(4,4,lambda i,j:S.Symbol('da'+str(i)+str(j)))
fq = [S.diff(f,qi) for qi in q]
Vq = [-g*ai[i] for i in range(4)]
Vnormal = A0/g+sum(fq[i]*ai[i] for i in range(4))
check('conditional_lift_normal', g*Vnormal+sum(fq[i]*Vq[i] for i in range(4))-A0)
divV = S.diff(A0/g,s)+sum(S.diff(fq[i],s)*ai[i]+fq[i]*ais[i] for i in range(4))
divV += sum(-S.diff(g,q[i])*ai[i]-g*aiq[i,i] for i in range(4))
Da = sum(aiq[i,i]-fq[i]*ais[i]/g for i in range(4))
check('conditional_lift_divergence', divV-g*(R-Da))

# Rational normal trace: no residue at infinity for s^2 ds/(2 f^2).
h,b,c = S.symbols('H B C')
ff = h+b*s+c*s**3
gg = S.diff(ff,s)
inv = S.invert(gg,ff,s)
rr = S.rem(b*s*inv**3,ff,s)
trace_s2 = -2*b/c
trace_rr = 3*rr.coeff(s,0)+trace_s2*rr.coeff(s,2)
check('source_trace_zero', trace_rr)

# Full order-36 diagonal quotient; all original coefficients are retained.
z,U,KK,t,p = S.symbols('z U K t p')
theta36 = S.Matrix((x**3,Y1/(x*y),a*Y2/(x*y),a**6,x**2*y**2))
J36 = theta36.jacobian(physical).det()
check('full_G36_jacobian', J36-36*a**6*x**2/y)
H36=1+z**2+t
B36=U/2+KK/3+z*U*KK/2
C36=z**-2+U**6+KK**6/t
f36=H36+B36*p+C36*p**3
pull36=dict(zip((z,U,KK,t,p),theta36))
check('full_G36_target', f36.subs(pull36,simultaneous=True)-F)
check('full_G36_actual_source', (p**2/(36*t*z**2)).subs(pull36,simultaneous=True)*J36-y**3)
rho=1/(18*t*z**2)
check('full_G36_residue', S.diff(p**2/(36*t*z**2*S.diff(f36,p)),p)/S.diff(f36,p)-rho*B36*p/S.diff(f36,p)**3)
check('full_G36_density_z', S.diff(rho,z)/rho+2/z)
check('full_G36_density_t', S.diff(rho,t)/rho+1/t)

result = {
    'status':'passed', 'arithmetic':'exact SymPy rational functions and generic first jets',
    'checks':checks, 'source':'B*s/(3*C*s^2+B)^3',
    'normal_order':'df first; ambient dx da ds du dv',
    'scope':'Source and conditional lift only; no primitive or certificate.',
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_name('actual-source-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
