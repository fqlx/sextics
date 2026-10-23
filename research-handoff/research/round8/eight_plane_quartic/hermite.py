"""Universal exact P1 Hermite reduction and source-preserving Ferrari flag."""
from pathlib import Path
import sympy as s,pickle,json,time
from sympy.polys.matrices import DomainMatrix
root=Path(__file__).parent;start=time.monotonic()
z=s.symbols('z');g=s.symbols('g0:5');G=sum(g[i]*z**i for i in range(5));N=(z*z-1)**3
pp=s.symbols('P0:4');bb=s.symbols('B0:3');P=sum(pp[i]*z**i for i in range(4));B=sum(bb[i]*z**i for i in range(3))
eq=s.Poly(s.diff(P,z)*G-P*s.diff(G,z)+B*G-N,z)
M,rhs=s.linear_eq_to_matrix([eq.nth(i)for i in range(7)],pp+bb)
MM,RR=DomainMatrix.from_Matrix(M).unify(DomainMatrix.from_Matrix(rhs))
num,den=MM.solve_den(RR)
den=s.sympify(den.as_expr()if hasattr(den,'as_expr')else den)
sol=[s.factor(a/den)for a in num.to_Matrix()]
Pout=sum(sol[i]*z**i for i in range(4));Bout=sum(sol[4+i]*z**i for i in range(3))
assert s.cancel(s.diff(Pout,z)*G-Pout*s.diff(G,z)+Bout*G-N)==0
Delta=s.discriminant(G,z)
assert all(s.cancel(s.denom(a)/Delta).is_rational_function(*g)for a in sol)
# In the tracezero basis 1/G',z/G',z²/G', the source is simply the three B_i.
# Lagrange's trace formula gives Tr(B/G')=[z³]B/g4=0.

# Ordinary power-basis coefficients of rho=B/G', obtained in the quartic
# algebra.  Keep this small linear circuit instead of expanding physical
# base-variable denominators.
Gp=s.diff(G,z)
mult=s.Matrix([[s.Poly(s.rem(Gp*z**j,G,z),z).nth(i)for j in range(4)]for i in range(4)])
assert s.factor(mult.det()-Delta/g[4]**2)==0
rho=s.factor(mult.inv()*s.Matrix(sol[4:]+[0]))
# Do not expand rho here: its source-bound definition via mult is exact.

# Independent flag/Ferrari identity on generic labeled depressed roots.
t1,t2,t3=s.symbols('t1 t2 t3');t4=-t1-t2-t3;roots=[t1,t2,t3,t4]
p=sum(roots[i]*roots[j]for i in range(4)for j in range(i+1,4))
q=-sum(roots[i]*roots[j]*roots[k]for i in range(4)for j in range(i+1,4)for k in range(j+1,4))
r=s.prod(roots);a1,a2,a3=s.symbols('a1 a2 a3');a0=(2*p*a2+3*q*a3)/4
rr=lambda t:a0+a1*t+a2*t*t+a3*t**3
assert s.expand(sum(rr(t)for t in roots))==0
f=lambda y:a1-q*a2/y-(y+3*p)*a3/2
for i in range(4):
    for j in range(i+1,4):
        w=roots[i]+roots[j];y=w*w
        assert s.cancel(rr(roots[i])+rr(roots[j])-w*f(y))==0
        assert s.expand(y**3+2*p*y*y+(p*p-4*r)*y-q*q)==0
    back=sum((roots[i]+roots[j])*f((roots[i]+roots[j])**2)for j in range(4)if i!=j)/2
    assert s.cancel(back-rr(roots[i]))==0

packet=dict(z=z,g=g,G=G,N=N,Delta=Delta,P_coefficients=sol[:4],B_coefficients=sol[4:],
            hermite_matrix=M,hermite_rhs=rhs,rho_multiplication_matrix=mult,rho_power_coefficients=list(rho),
            source_factor=-s.Rational(1,512),
            ferrari='y³+2p y²+(p²-4r)y-q²=0; w²=y',
            ferrari_source='f(y)=a1-q*a2/y-(y+3p)*a3/2; actual anti source=-w*f(y)/512',
            inverse='rho(t_i)=1/2 sum_{j!=i}(t_i+t_j) f((t_i+t_j)^2)',
            charge='nabla_i=partial_i+(partial_i y)/(2y)')
(root/'hermite.pickle').write_bytes(pickle.dumps(packet))
ans=dict(hermite_identity=True,P_coefficients=[str(a)for a in sol[:4]],B_coefficients=[str(a)for a in sol[4:]],
         source_trace_zero=True,tracezero_basis=['1/Gprime','z/Gprime','z²/Gprime'],
         ferrari_pair_trace=True,ferrari_cubic=True,ferrari_inverse_half_trace=True,
         source_factor='-1/512',seconds=time.monotonic()-start,
         scope='Exact generic rational-form/finite-field correspondence; no primitive or coniveau inference.')
(root/'hermite.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps({k:v for k,v in ans.items()if'coefficients'not in k},indent=2),flush=True)
