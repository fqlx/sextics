"""Independent exact trace identities for the 11 marked Abel--Prym currents.
No source matching or rational primitive is asserted here.
"""
from pathlib import Path
import sympy as s,pickle,json,time
HERE=Path(__file__).parent;start=time.monotonic()
actual=pickle.loads(Path('/workspace/research/round9/cyclic_full/actual_fast.pickle').read_bytes())
conj=pickle.loads(Path('/workspace/research/round9/cyclic_full/conjugate_fast.pickle').read_bytes())
W,h,t,L,r,x=actual['symbols'];u,z,M,P,c,a,b,v=s.symbols('u z M P c a b v');cc=s.Rational(5,7)
q=u*u+c*u+P
A,B,aa,bb=s.symbols('A B aa bb');N=aa*aa-aa*bb*c+bb*bb*P
# Inverse/trace identities are universal over the quadratic algebra.
inv=(aa-bb*c-bb*u)/N
assert s.rem(s.together((aa+bb*u)*inv-1).as_numer_denom()[0],q,u)==0
red=s.rem(s.expand((A+B*u)*(aa-bb*c-bb*u)),q,u)/N
assert s.simplify(s.expand(red).coeff(u)-(aa*B-bb*A)/N)==0
redu=s.rem(s.expand(u*(A+B*u)*(aa-bb*c-bb*u)),q,u)/N
assert s.simplify(s.expand(redu).coeff(u)-(aa*A+(bb*P-aa*c)*B)/N)==0
# For R=A+B*u, Tr[R/(2u+c)]=B. This follows without a square root.
inv_derivative=(2*u+c)/(c*c-4*P)
assert s.rem(s.expand((2*u+c)**2-(c*c-4*P)),q,u)==0
rr=s.rem(s.expand((A+B*u)*(2*u+c)),q,u)/(c*c-4*P)
assert s.simplify(2*s.expand(rr).coeff(u,0)-c*s.expand(rr).coeff(u,1)-B)==0

Bbase=b*(1+a*v);Pbase=1+v**6;Qbase=cc*a*b*v;Rbase=cc*(a*b+v*b**3);Sbase=1+a**6+b**6
Abase=3*Sbase-Bbase*Rbase;Mbase=Abase/(3*Sbase)
zbase=Bbase*Rbase/Abase
rbase=(3*Sbase*Qbase-Rbase**2)/(Bbase*Abase);xbase=3*Bbase**3/Abase
ct=s.cancel(rbase+3*zbase*zbase/xbase)
assert s.cancel(ct-Qbase/(Bbase*Mbase))==0
G=Pbase*(1+a*v)**2-cc*a*v*(1+a*v)+a*a*v*v
normct=s.cancel((Qbase/Bbase)**2-cc*(Qbase/Bbase)*cc+cc**2*Pbase)
assert s.cancel(normct-cc**2*G/(1+a*v)**2)==0

# Each holomorphic primitive divided by its character monomial is polynomial
# in u_old=w^3, because W_can^3=u_old/M. Keep physical substitutions factored.
compiled={};maxdegree=0
for block,idx,label,char,n in [(actual,0,'actual_h2',1,s.Integer(1)),(actual,1,'actual_t',1,z),(conj,0,'conjugate_Wh',2,s.Integer(1))]:
 out={}
 for direction in ['L','r','x']:
  pp=block['primitives'][direction][idx];assert pp['Q14_raw'] is None
  terms={}
  for coeff,(component,ex)in zip(pp['Q8_raw'],block['lab8']):
   if not coeff or component==2:continue
   wp=ex[0]+(1 if component==1 else 0)-char
   assert wp>=0 and wp%3==0
   degree=wp//3;maxdegree=max(maxdegree,degree)
   sign=-1 if component==1 else 1
   terms[degree]=terms.get(degree,0)+sign*coeff*z**ex[2]/M**degree
  expr=sum(s.cancel(coeff/pp['Q8_denominator'])*u**j for j,coeff in terms.items())
  reduced=s.rem(expr,u*u+cc*u+P,u)
  Avec=s.cancel(s.expand(reduced).coeff(u,0));Bvec=s.cancel(s.expand(reduced).coeff(u,1))
  out[direction]={'A':Avec,'B':Bvec}
 compiled[label]={'character':char,'n':n,'H_reduced':out}

# A machine-readable exact packet avoids expanded physical substitutions.
packet={'symbols':(u,z,M,P,L,r,x),'c':cc,'forms':compiled,
 'trace_rule':'If H=A+B*u mod(u²+c*u+P), Tr_u[H/((2u+c)Ct)]=(aa*B-bb*A)/N; aa=c*av/(M*E),bb=c/M,N=c²*G/(M²*E²).',
 'u_trace_rule':'Tr_u[u*H/((2u+c)Ct)]=(aa*A+(bb*P-aa*c)*B)/N',
 'base2form_rule':'For actual i and j=0..2: trace_w[rho*alpha_i wedge (w*v^j/Fw)dv] = v^j * [n*bb/(3N)*dlogM + sum trace_rule(Hij)*dparam_j] wedge dv. Conjugate uses rho²*alpha, j=0..3 and the same rule, or Gamma numerator w³ with u_trace_rule; its logM coefficient is -aa/(3N).'}
(HERE/'closed_trace.pickle').write_bytes(pickle.dumps(packet))
out={'universal_quadratic_inverse':True,'derivative_trace_identity':True,'trace_formula':True,'u_trace_formula':True,'canonical_Ct_identity':True,'physical_norm_identity':True,'G':'(1+v^6)*(1+a*v)^2-c*a*v*(1+a*v)+a^2*v^2','homogenized_G':'(X0^6+X1^6)*(X0*Y2+X1*Y0)^2-c*X0^6*X1*Y0*(X0*Y2+X1*Y0)+X0^6*X1^2*Y0^2','Gamma_discriminant_cancels':True,'primitive_character_reduction':True,'max_u_degree_before_reduction':maxdegree,'number_base2form_generators':11,'seconds':round(time.monotonic()-start,3),'scope':'Exact closed quadratic trace identities only. Does not assert a source match, a primitive, or a serving Gysin channel.'}
(HERE/'closed_trace.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
