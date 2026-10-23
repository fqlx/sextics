"""Smaller actual-source quotient using the global Y sign involution."""
from pathlib import Path
import sympy as s,pickle,json,time
from sympy.polys.matrices import DomainMatrix
from flint import nmod_poly
root=Path(__file__).parent;start=time.monotonic()
old=pickle.loads((root/'model.pickle').read_bytes());F,A=old['F'],old['A']
X=s.symbols('X0:3');Y=s.symbols('Y0:3');k,y,t,a,b,c,d,eps=s.symbols('k y t a b c d eps')
coords=[k,k*a,k*b,k*y,k*y*c,k*y*d]
J=s.factor(s.Matrix(coords).jacobian([k,y,a,b,c,d]).det());assert J==k**5*y*y
FF=s.Poly(s.expand(F.subs(dict(zip(X+Y,[z.subs(k,1)for z in coords])),simultaneous=True)),y)
assert all(e[0]%2==0 for e,co in FF.terms())
C=s.Poly(sum(co*t**(e[0]//2)for e,co in FF.terms()),t);assert C.degree()==3
cc=[s.factor(C.nth(i))for i in range(4)]
assert s.expand(A.subs(dict(zip(X+Y,coords)),simultaneous=True)-k**6*y**3)==0
# Euler contraction supplies the extra k; on k=1, dy=dt/(2y).
assert s.cancel(y**3*J.subs(k,1)/(2*y)-y**4/2)==0

g=s.symbols('g0:4');G=sum(g[i]*t**i for i in range(4));N=t*t
pc=s.symbols('P0:3');bc=s.symbols('B0:2');P=sum(pc[i]*t**i for i in range(3));B=sum(bc[i]*t**i for i in range(2))
eq=s.Poly(s.diff(P,t)*G-P*s.diff(G,t)+B*G-N,t)
M,RHS=s.linear_eq_to_matrix([eq.nth(i)for i in range(5)],pc+bc)
MM,RR=DomainMatrix.from_Matrix(M).unify(DomainMatrix.from_Matrix(RHS));num,den=MM.solve_den(RR)
den=MM.domain.to_sympy(den);sol=[s.factor(z/den)for z in num.to_Matrix()]
assert s.cancel(s.diff(sum(sol[i]*t**i for i in range(3)),t)*G-sum(sol[i]*t**i for i in range(3))*s.diff(G,t)+sum(sol[3+i]*t**i for i in range(2))*G-N)==0
Gp=s.diff(G,t);mult=s.Matrix([[s.Poly(s.rem(Gp*t**j,G,t),t).nth(i)for j in range(3)]for i in range(3)])
rho=mult.inv()*s.Matrix(sol[3:]+[0]);rho=[s.factor(z)for z in rho]
shift=-g[2]/(3*g[3]);p=g[1]/g[3]-g[2]**2/(3*g[3]**2)
q=2*g[2]**3/(27*g[3]**3)-g[2]*g[1]/(3*g[3]**2)+g[0]/g[3]
beta=s.symbols('beta0:3');aa=[s.expand(sum(beta[j]*s.binomial(j,i)*shift**(j-i)for j in range(i,3)))for i in range(3)]

# Exact Cardano/Fourier identities, retaining both conjugate charge sectors.
al,be,eta,a1,a2=s.symbols('alpha beta eta a1 a2');pp=-3*al*be;qq=-al**3-be**3;a0=2*pp*a2/3
red=lambda pol:s.rem(s.Poly(s.expand(pol),eta),s.Poly(eta*eta+eta+1,eta)).as_expr()
rr=lambda z:a0+a1*z+a2*z*z
chi1=a1*al+a2*be*be;chi2=a1*be+a2*al*al
roots=[al+be,eta*al+eta**2*be,eta**2*al+eta*be]
for i,rt in enumerate(roots):
    assert red(rt**3+pp*rt+qq)==0
    assert red(rr(rt)-eta**i*chi1-eta**(2*i)*chi2)==0
assert red(sum(eta**(2*i)*rr(rt)for i,rt in enumerate(roots))/3-chi1)==0
assert s.cancel(chi1/al-a1-pp*pp*a2/(9*al**3))==0

# Independently check a concrete physical good fiber modulo 101.
prime=101;mod=lambda x:int(s.numer(s.cancel(x)))%prime*pow(int(s.denom(s.cancel(x))),-1,prime)%prime
sample={a:1,b:2,c:3,d:5};gs=[mod(z.subs(sample))for z in cc];sub=dict(zip(g,gs));GG=nmod_poly(gs,prime)
assert GG.degree()==3 and GG.gcd(GG.derivative()).degree()==0
PP=nmod_poly([mod(z.subs(sub))for z in sol[:3]],prime);BB=nmod_poly([mod(z.subs(sub))for z in sol[3:]],prime)
assert PP.derivative()*GG-PP*GG.derivative()+BB*GG==nmod_poly([0,0,1],prime)
betav=[mod(z.subs(sub))for z in rho];av=[mod(z.subs(sub|dict(zip(beta,betav))))for z in aa]
pv,qv=[mod(z.subs(sub))for z in (p,q)];assert (3*av[0]-2*pv*av[2])%prime==0
packet=dict(symbols=dict(k=k,y=y,t=t,a=a,b=b,c=c,d=d,eps=eps),F=F,A=A,C=C.as_expr(),coefficients=cc,
            Jacobian=J,source_factor=s.Rational(1,2),source_numerator=t*t,
            source='+(t²/2) dt wedge da db dc dd/C(t)^2, degree(C)=3',
            actual_normal_deformation='C3(y²)+eps*y³; -d_eps[y²dy/F_eps] at0 descends to t²dt/(2C3²)',
            universal=dict(g=g,G=G,N=N,P_coefficients=sol[:3],B_coefficients=sol[3:],rho_power_coefficients=rho,
                           beta_symbols=beta,rho_depressed_coefficients=aa,p=p,q=q,shift=shift),
            cardano=dict(discriminant='D²=q²/4+p³/27',W='-q/2+D',w='w³=W',
                         source='w*(a1+p²*a2/(9W))',conjugate='wbar=-p/(3w); conjugate first charge supplies the second',
                         charge='d+(1/3)*dlogW',source_factor='1/2',
                         inverse='rho(t_i)=eta^i*chi1+eta^(-i)*chi2; chi1=(1/3)sum_i eta^(-i)rho(t_i)'),
            instance_rec_sha256=old['instance_rec_sha256'])
(root/'cubic_model.pickle').write_bytes(pickle.dumps(packet))
ans=dict(exact_record_bound=True,instance_rec_sha256=old['instance_rec_sha256'],full_Jacobian=str(J),
         source='+(t²/2) dt wedge d⁴base/C3(t)^2',cubic_coefficient_term_counts=[len(s.Poly(z,a,b,c,d).terms())for z in cc],
         universal_P=[str(z)for z in sol[:3]],universal_B=[str(z)for z in sol[3:]],
         trace_zero=True,rank=2,Cardano_Fourier_identities=True,
         good_fiber=dict(prime=prime,point=list(sample.values()),C=gs,P=list(map(int,PP)),B=list(map(int,BB)),rho=betav,pq=[pv,qv],depressed_rho=av),
         seconds=time.monotonic()-start,scope='Exact actual-source cubic quotient and charge transfer, no primitive or certificate.')
(root/'cubic_model.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
