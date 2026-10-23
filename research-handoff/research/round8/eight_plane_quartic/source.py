"""Bind the tracezero Ferrari source to the exact eight-plane quartic.

The generic source is deliberately an arithmetic circuit: substitute the five
physical coefficients only after evaluating or differentiating the small
universal expressions.  Expanding a four-variable discriminant is unnecessary.
"""
from pathlib import Path
import sympy as s,pickle,json,time
from flint import nmod_poly
root=Path(__file__).parent;start=time.monotonic()
model=pickle.loads((root/'model.pickle').read_bytes())
herm=pickle.loads((root/'hermite.pickle').read_bytes())
g=herm['g'];a,b,c,d,e=g[4],g[3],g[2],g[1],g[0]
p=c/a-3*b*b/(8*a*a)
q=d/a-b*c/(2*a*a)+b**3/(8*a**3)
r=e/a-b*d/(4*a*a)+b*b*c/(16*a**3)-3*b**4/(256*a**4)
beta=s.symbols('beta0:4');shift=-b/(4*a)
aa=[s.expand(sum(beta[k]*s.binomial(k,j)*shift**(k-j) for k in range(j,4)))for j in range(4)]
ff=[aa[1]-3*p*aa[3]/2-aa[2]*(p*p-4*r)/q,
    -aa[3]/2-2*p*aa[2]/q,-aa[2]/q]
P,Q,R,y=s.symbols('p q r y');res=y**3+2*P*y*y+(P*P-4*R)*y-Q*Q
invprime=s.invert(s.diff(res,y),res,y)
invy=(y*y+2*P*y+P*P-4*R)/(Q*Q)
connections={}
for name,par in [('p',P),('q',Q),('r',R)]:
    cols=[]
    for j in range(3):
        power=y**(j-1) if j else invy
        expr=s.rem(-s.Rational(2*j+1,2)*power*s.diff(res,par)*invprime,res,y)
        cols.append([s.factor(s.Poly(expr,y).nth(i))for i in range(3)])
    connections[name]=s.Matrix.hstack(*[s.Matrix(v)for v in cols])

# A good physical fiber is checked by a second, finite-field implementation.
prime=101;gs=[72,85,23,2,37];sub=dict(zip(g,gs))
mod=lambda x:int(s.numer(s.cancel(x)))%prime*pow(int(s.denom(s.cancel(x))),-1,prime)%prime
GG=nmod_poly(gs,prime);N=nmod_poly([-1,0,3,0,-3,0,1],prime)
pc=[mod(v.subs(sub))for v in herm['P_coefficients']]
bc=[mod(v.subs(sub))for v in herm['B_coefficients']]
PP=nmod_poly(pc,prime);BB=nmod_poly(bc,prime)
assert PP.derivative()*GG-PP*GG.derivative()+BB*GG==N
rho=(BB*GG.derivative().xgcd(GG)[1])%GG
rhoc=list(map(int,rho))+[0]*(4-len(rho))
allsub=sub|dict(zip(beta,rhoc))
aval=[mod(v.subs(allsub))for v in aa]
pqr=[mod(v.subs(sub))for v in [p,q,r]]
assert (4*aval[0]-2*pqr[0]*aval[2]-3*pqr[1]*aval[3])%prime==0
fv=[mod(v.subs(allsub))for v in ff]
RR=nmod_poly([-pqr[1]**2,pqr[0]**2-4*pqr[2],2*pqr[0],1],prime)
assert RR.gcd(RR.derivative()).degree()==0
assert any(fv)

packet=dict(model=model,hermite=herm,quartic_depression=dict(p=p,q=q,r=r,shift=shift),
            beta_symbols=beta,rho_t_coefficients=aa,f_polynomial_coefficients=ff,
            resolvent_symbols=dict(p=P,q=Q,r=R,y=y),resolvent=res,
            charged_connections=connections,
            physical_substitution=dict(zip(g,model['coefficients'])),
            source_factor=-s.Rational(1,512),
            current_equation='sum_i (partial_i + y_i/(2*y))*u_i = -f(y)/512',
            current_derivative='y_i=-(partial_i R)(y)/R_y(y), with p,q,r from the physical quartic',
            finite_flag_inverse='rho(t_i)=1/2 sum_{j!=i}(t_i+t_j)*f((t_i+t_j)^2)')
(root/'source.pickle').write_bytes(pickle.dumps(packet))
ans=dict(good_prime=prime,good_quartic=gs,P_coefficients=pc,B_coefficients=bc,
         rho_z_coefficients=rhoc,depressed_pqr=pqr,rho_t_coefficients=aval,
         f_y_coefficients=fv,resolvent_coefficients=list(map(int,RR)),
         actual_source_factor='-1/512',source_nonzero=True,source_trace_zero=True,
         finite_field_hermite_identity=True,resolvent_squarefree=True,
         generic_source='rho=M_Gprime^-1*(B0,B1,B2,0); beta_j=[z^j]rho',
         generic_f=['a1-3*p*a3/2-a2*(p^2-4*r)/q','-a3/2-2*p*a2/q','-a2/q'],
         universal_connections={name:[[str(v)for v in mat.row(i)]for i in range(3)]for name,mat in connections.items()},
         finite_flag_inverse=packet['finite_flag_inverse'],seconds=time.monotonic()-start,
         scope='Exact source and charged rank3 connection. No rational current or coniveau claim.')
(root/'source.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps({k:v for k,v in ans.items()if k!='universal_connections'},indent=2))
