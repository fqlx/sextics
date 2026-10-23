"""Concrete actual-coordinate differentiation audit, independent of the producer.
Uses native exact fractions to retain arbitrary rational base/p dependence.
The target test current has a NONZERO obstruction and is not a primitive.
"""
from pathlib import Path
import json,time
import flint

start=time.monotonic()
CTX=flint.fmpq_mpoly_ctx.get(['x','y','z','e','b'])
class Q:
 def __init__(self,n=0,d=1):
  if isinstance(n,Q):self.n,self.d=n.n,n.d;return
  self.n=n if isinstance(n,flint.fmpq_mpoly)else CTX.constant(n)
  self.d=d if isinstance(d,flint.fmpq_mpoly)else CTX.constant(d)
  if not self.d:raise ZeroDivisionError
  if not self.n:self.d=CTX.constant(1);return
  g=self.n.gcd(self.d);self.n=self.n//g;self.d=self.d//g
 def __add__(self,o):
  o=Q(o);g=self.d.gcd(o.d)
  return Q(self.n*(o.d//g)+o.n*(self.d//g),(self.d//g)*o.d)
 __radd__=__add__
 def __neg__(self):return Q(-self.n,self.d)
 def __sub__(self,o):return self+-Q(o)
 def __rsub__(self,o):return Q(o)+-self
 def __mul__(self,o):
  o=Q(o);g=self.n.gcd(o.d);h=o.n.gcd(self.d)
  return Q((self.n//g)*(o.n//h),(self.d//h)*(o.d//g))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=Q(o)
  if not o.n:raise ZeroDivisionError
  return self*Q(o.d,o.n)
 def __rtruediv__(self,o):return Q(o)/self
 def __pow__(self,k):return Q(self.n**k,self.d**k)if k>=0 else Q(self.d**(-k),self.n**(-k))
 def diff(self,i):return Q(self.n.derivative(i)*self.d-self.n*self.d.derivative(i),self.d*self.d)
 def __bool__(self):return bool(self.n)
 def at(self,p):return self.n(*p)/self.d(*p)

x,y,z,e,b=map(Q,CTX.gens());p=e*b
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3
A=y**3
R=e**6+b**6;Z=e**6-b**6;L=H+C*p;F=R+L;ff=L**2-4*p**6
q=[x*p/(1+p),y+z*p,z*p**2/(1+x)]
s=(x+y*z)*p**2/(1+p)
sp=(x+y*z)*p*(p+2)/(1+p)**2
qh=sum(qi*H.diff(i)for i,qi in enumerate(q))
qc=sum(qi*C.diff(i)for i,qi in enumerate(q))
dq=sum(qi.diff(i)for i,qi in enumerate(q))
E=ff*(dq-sp)-L*(qh+p*qc)+s*(C*L-12*p**5)+A*L/6
M=A-6*qh-6*p*qc
K=M+6*s*(3*R+C*p)/p
ve=-3*s*e/p+K*e/(6*Z)
vb=-3*s*b/p-K*b/(6*Z)
vector=[6*qi for qi in q]+[ve,vb]
normal=sum(vi*F.diff(i)for i,vi in enumerate(vector))
divergence=sum(vi.diff(i)for i,vi in enumerate(vector))
Qstar=(6*(R-L)*(dq-sp)-M-6*s*C)/Z**2
checks={
 'actual_immutable_affine_F':not(F-(1+x**6+y**6+z**6+e**6+b**6+x*y*z/2+x**3*z*e*b/2+x*y*e*b/3)),
 'q_has_every_base_and_endpoint_dependence':all(any(qi.diff(i)for qi in q)for i in range(4)),
 's_has_every_base_and_endpoint_dependence':all(s.diff(i)for i in range(4)),
 'DIRECT_endpoint_partial_s_p':not(s.diff(3)/b-sp),
 'DIRECT_five_coordinate_normal':not(normal-A),
 'DIRECT_five_coordinate_divergence':not(divergence-6*E/Z**2-F*Qstar),
 'DIRECT_complete_localization_identity':not(A-normal+F*divergence-6*F*E/Z**2-F**2*Qstar),
 'arbitrary_current_has_NONZERO_target_obstruction':bool(E),
}
point=[1,2,1,2,1]
checks['actual_vector_test_denominators_nonzero']=all(v.d(*point)!=0 for v in vector+[E,Qstar])
# Direct nonzero auxiliary-source test with E=0, distinct from target A=y^3.
V=[C.diff(1),-C.diff(0),Q(0)]
Aaux=sum(vi*H.diff(i)for i,vi in enumerate(V))
qaux=[vi/6 for vi in V]
qhaux=sum(qi*H.diff(i)for i,qi in enumerate(qaux))
qcaux=sum(qi*C.diff(i)for i,qi in enumerate(qaux))
Eaux=ff*sum(qi.diff(i)for i,qi in enumerate(qaux))-L*(qhaux+p*qcaux)+Aaux*L/6
Vactual=V+[Q(0),Q(0)]
checks['NONTRIVIAL_E0_auxiliary_source']=bool(Aaux)and not Eaux
checks['E0_extracted_vertical_components_zero']=not(Aaux-6*qhaux-6*p*qcaux)
checks['DIRECT_E0_auxiliary_normal']=not(sum(vi*F.diff(i)for i,vi in enumerate(Vactual))-Aaux)
checks['DIRECT_E0_auxiliary_divergence']=not(sum(vi.diff(i)for i,vi in enumerate(Vactual)))
assert all(checks.values()),checks
out={
 'status':'INDEPENDENT_ACTUAL_DIFFERENTIATED_VECTOR_AUDIT_PASS; ORIGINAL_TARGET_CURRENT_OPEN',
 'method':'Native exact fractions in Q(x,y,z,e,b). Set p=e*b BEFORE constructing and literally differentiating all five ambient vector components. No q(H),q(C),div(q) placeholders or imported producer implementation enter the derivative.',
 'actual_F':'1+x6+y6+z6+e6+b6+xyz/2+x3*z*e*b/2+xy*e*b/3','actual_A':'y3',
 'current_q':['x*p/(1+p)','y+z*p','z*p²/(1+x)'],'current_s':'(x+y*z)*p²/(1+p)',
 'general_scope':'Arbitrary rational base/p dependence in q and s, including higher odd Z poles absorbed by Z²=f on the endpoint. This q-vector is not the certificate pole parameter; the immutable problem here has pole parameter one.',
 'independent_general_reason':'For T=e*d_e+b*d_b,D=e*d_e-b*d_b, D(p)=0,D(R)=6Z,D(Z)=6R,T(p)=2p. D annihilates all rational base/p coefficient dependence. Vertical divergence is -6s_p+18s/p-KR/Z²; Z²-f=F(R-L) yields the complete extraction identity.',
 'actual_test_point':dict(zip(['x','y','z','e','b'],map(str,point))),
 'point_values':{'normal':str(normal.at(point)),'divergence':str(divergence.at(point)),'E':str(E.at(point)),'Qstar':str(Qstar.at(point))},
 'E0_conditional_test':'Aaux=C_y*H_x-C_x*H_y !=0, q=(C_y,-C_x,0)/6,s=0. Its extracted vertical components vanish, and V=(C_y,-C_x,0,0,0) is directly divergence-free with dF(V)=Aaux. Aaux is NOT the immutable source y^3.',
 'limitations':'Extraction infrastructure only. The globally differentiated Y+CM+Green target prefix has E!=0. Homogenization, degrees and complex-coprimality remain required for any future closed target current.',
 'checks':checks,'check_count':len(checks),'elapsed_seconds':round(time.monotonic()-start,3),
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'independent actual five-coordinate differentiated-vector checks; no target solve',flush=True)
