#!/usr/bin/env python3
"""Exact closed-twoform current and its full remaining source.

The checks use formal coefficient brackets and their directional derivatives,
so they retain derivatives of Q rather than evaluating or dropping them.
"""
import sympy as S

p,H,B,C,A,D,E,nq,t0 = S.symbols('p H B C A D E nq t0')
g=B+3*C*p**2
Q=A+3*p**2*D+2*p**3*E
NH=p*A+p**3*D
NB=-A+p**3*E
NC=-D-p*E
Qp=S.diff(Q,p)

def zero(x):
    assert S.cancel(x)==0

zero(Qp+6*p*NC)
zero(NB+3*p**2*NC+Q)

# nq=N(Q), t0={g,Q}_0, with base bracket holding p constant.
# Extended-bracket chain rule has all implicit p derivatives included.
NS=p*NB/Q-B*p*nq/Q**2
gQ=t0+(6*C*p*nq+Qp*Q)/g
Fg=-p/g+p**2*gQ/(2*Q**2)  # {F,g}, F=p^2/(2Q)
remaining=NS/g**2-Fg/g
expected=-p*(2*nq+p*t0)/(2*Q**2*g)
zero(remaining-expected)

# Further closed-Q correction, retaining implicit p derivatives.
FlogQ=p*nq/(Q**2*g)  # {p^2/(2Q),log Q}
zero(remaining+FlogQ+p**2*t0/(2*Q**2*g))

# lambda+F*dlogQ differs from the simpler potential only by -dF.
# Formal cotangent basis (dp,dB,dC,dQ).
lam=S.Matrix([-p/Q,-p**2/(2*Q*g),-3*p**4/(2*Q*g),0])
dF=S.Matrix([p/Q,0,0,-p**2/(2*Q**2)])
Flog=S.Matrix([0,0,0,p**2/(2*Q**2)])
lamtilde=S.Matrix([0,-p**2/(2*Q*g),-3*p**4/(2*Q*g),0])
for x in lam+Flog+dF-lamtilde:
    zero(x)

# Equivalence of the two base-bracket descriptions of the numerator.
qH,qB,qC=S.symbols('qH qB qC')
zero((2*nq+p*t0).subs({nq:qH+p*qB+p**3*qC,
                         t0:-qB-3*p**2*qC})
     -(2*qH+p*qB-p**3*qC))

# Equality of the two lambda representations after df=0.
# Coefficients are in the formal basis (dp,dH,dB,dC).
lam1=S.Matrix([-B*p/(Q*g),0,0,0])
lam1-=p**2/(2*Q*g)*S.Matrix([6*C*p,0,1,3*p**2])
lam2=S.Matrix([0,p/(Q*g),p**2/(2*Q*g),-p**4/(2*Q*g)])
df=S.Matrix([g,1,p,p**3])
for x in lam1-lam2+p*df/(Q*g):
    zero(x)

# Actual branch residue: Res eta_old=-d_D[(p^2/(2Q))*omega_D].
branch={B:-3*C*p**2,H:2*C*p**3}
delta_p=18*C*p**2*Q
delta_Q=108*C**2*p**3*nq-108*C*p**3*Q*NC
delta_F=p*delta_p/Q-p**2*delta_Q/(2*Q**2)
zero((NS/Q+delta_F/delta_p).subs(branch))

# Component convention is fixed independently of Hamiltonian naming.
z,U,K,t=S.symbols('z U K t', nonzero=True)
fz,fU,fK,ft=S.symbols('fz fU fK ft')
om=S.Matrix([[0,1/(3*z**2),0,0],[-1/(3*z**2),0,0,0],
             [0,0,0,1/(6*t)],[0,0,-1/(6*t),0]])
N=S.Matrix([3*z**2*fU,-3*z**2*fz,6*t*ft,-6*t*fK])
assert list((N.T*om).T)==[fz,fU,fK,ft]

# H,B,C,t form a legal generic coordinate chart; no hidden g-order is
# introduced when pulling the actual base volume to the cubic cover.
Hp=1+z**2+t
Bp=U/2+K/3+z*U*K/2
Cp=z**-2+U**6+K**6/t
minor=S.Matrix([Hp,Bp,Cp]).jacobian([z,U,K]).det()
assert minor.subs({z:1,U:1,K:1,t:2})==-4

def base_bracket(a,b):
    return (3*z**2*(S.diff(a,z)*S.diff(b,U)-S.diff(a,U)*S.diff(b,z))
            +6*t*(S.diff(a,K)*S.diff(b,t)-S.diff(a,t)*S.diff(b,K)))
gp=Bp+3*Cp*p**2
Qphys=base_bracket(Hp,Bp)+3*p**2*base_bracket(Hp,Cp)+2*p**3*base_bracket(Bp,Cp)
Tphys=base_bracket(gp,Qphys)
sample={z:1,U:1,K:1,t:2}
sample_f=(Hp+Bp*p+Cp*p**3).subs(sample)
sample_T=S.rem(S.expand(Tphys.subs(sample)),sample_f,p)
zero(sample_T-(S.Rational(103707,5)*p**2+S.Rational(3778244,75)*p-S.Rational(73476,25)))
assert sample_T!=0

# Independent verifier's actual simple branch point.  Work modulo p^2=1/12.
branch_sample={z:1,U:-1,K:0,t:p/3-2}
branch_rel=p**2-S.Rational(1,12)
def at_branch(expr):
    num,den=S.cancel(expr.subs(branch_sample)).as_numer_denom()
    return S.rem(num,branch_rel,p),S.rem(den,branch_rel,p)
assert at_branch(Hp+Bp*p+Cp*p**3)[0]==0
assert at_branch(gp)[0]==0
assert at_branch(minor+2)[0]==0
assert at_branch(Qphys+8-S.Rational(5,6)*p)[0]==0
assert at_branch(S.diff(gp,p)-12*p)[0]==0

print('PASS: component signs, full global and Q-log corrections,')
print('      equivalent potentials, branch-residue primitive, branch chart,')
print('      nonzero physical remainder, and an actual simple branch point.')
