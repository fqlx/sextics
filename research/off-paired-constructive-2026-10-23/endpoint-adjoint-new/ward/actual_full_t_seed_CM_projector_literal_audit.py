"""Independent WHOLE full-source t-seed + actual CM-projector audit.

Every physical P,Q normal and exact endpoint fiber cochain is retained.
The actual sample evaluates the full four-row remainder; no closure asserted.
"""
from pathlib import Path
import json
import sympy as s

H,C,p,Z,fs,ft,Ht,Ct=s.symbols('H C p Z f ft Ht Ct',nonzero=True)
L=H+C*p;ff=L*L-4*p**6
Dp=lambda q:s.diff(q,p)+s.diff(q,Z)*(C*L-12*p**5)/Z
thetaH=-L/Z**3;thetaC=-p*L/Z**3
def endpoint_zero(q):
 n=s.together(q).as_numer_denom()[0]
 return s.factor(s.rem(n,Z*Z-ff,Z))==0
seed_derivative=ft/Z+fs*Ht*thetaH+fs*Ct*thetaC+fs*Ct*Dp(p/Z)/(2*C)
checks={'literal_FULL_t_seed_and_indispensable_fiber_cochain':endpoint_zero(
 seed_derivative-fs*(Ht-3*H*Ct/(2*C))*thetaH-(ft-fs*Ct/C)/Z)}

# Actual CM projector, with BOTH moving elliptic normals differentiated.
t,rho,h,y,alpha,zeta=s.symbols('t rho h y alpha zeta',nonzero=True)
den=(h-alpha*t)*(zeta*h-alpha*t)
kP=2*zeta*t*(y+rho)/den
kQ=2*(y+rho)*(alpha*t+zeta*zeta*h)/(alpha*alpha*den)
DP=lambda q:rho*s.diff(q,t)+3*t*t*s.diff(q,rho)
DQ=lambda q:y*s.diff(q,h)+s.Rational(3,2)*h*h*s.diff(q,y)
n=s.together(DP(kQ)-DQ(kP)-t).as_numer_denom()[0]
for v,rel in [(rho,rho*rho-2*t**3+1),(y,y*y-h**3+1),
              (zeta,zeta*zeta+zeta+1),(alpha,alpha**3-2)]: n=s.rem(n,rel,v)
checks['WHOLE_actual_CM_projector_curvature_P_AND_Q']=s.factor(n)==0

# The full current is m KP*dlogb*omega0.  Its derivative coefficient in
# eta,omegaQ,dlogb,dp is computed directly, before compact reduction.
m,mP,mQ,CP,CQ,HQ,kp,kq,dkpP,dkpQ=s.symbols('m mP mQ CP CQ HQ kP kQ DPkQ DQkP')
dCM=(mP*kq+m*dkpP-mQ*kp-m*dkpQ)/Z-m*kp*HQ*thetaH+m*(kq*CP-kp*CQ)*thetaC
A0=mQ*kp-mP*kq
AH=m*kp*HQ
AC=m*(kp*CQ-kq*CP)
Rliteral=A0/Z+AH*thetaH+AC*thetaC
checks['WHOLE_literal_projector_derivative_and_signed_remainder']=s.factor(
 (dCM+Rliteral-m*t/Z).subs(dkpP,t+dkpQ))==0

# Exact native rank4 projection PLUS its complete literal fiber primitive.
conn=json.loads((Path(__file__).parents[1]/'native_q_connection.json').read_text())
MH=s.Matrix([[s.sympify(q,locals={'H':H,'C':C}) for q in row] for row in conn['H']])
MC=s.Matrix([[s.sympify(q,locals={'H':H,'C':C}) for q in row] for row in conn['C']])
Delta=4*C**6-729*H**4
polyH=(-12*C**6*p-8*C**5*H+48*C**4*p**5-72*C**3*H*p**4
       +108*C**2*H**2*p**3-162*C*H**3*p**2+243*H**4*p)/(H*Delta)
polyC=(16*C**5*p+12*C**4*H-72*C**3*p**5+108*C**2*H*p**4
       -162*C*H**2*p**3+243*H**3*p**2)/Delta
bas=s.Matrix([1,p,p**3,p**4])
checks['literal_thetaH_ALL4_and_fiber_primitive']=endpoint_zero(thetaH-(bas.dot(MH[:,0]))/Z-Dp(polyH/Z))
checks['literal_thetaC_ALL4_and_fiber_primitive']=endpoint_zero(thetaC-(bas.dot(MC[:,0]))/Z-Dp(polyC/Z))
compact=A0*s.Matrix([1,0,0,0])+AH*MH[:,0]+AC*MC[:,0]
checks['WHOLE_rank4_plus_ALL_fiber_cochains']=endpoint_zero(Rliteral-bas.dot(compact)/Z-Dp((AH*polyH+AC*polyC)/Z))

# Three-dimensional exact physical Taylor jets at t=rho=R=z=1,U=5/2,W=-3/2.
# All third physical t derivatives needed by dRseed are present.
ORDER=4
class J:
 def __init__(self,q=0):
  self.a={i:s.Rational(v) for i,v in q.items() if v!=0 and sum(i)<=ORDER} if isinstance(q,dict) else ({(0,0,0):s.Rational(q)} if q!=0 else {})
 @staticmethod
 def co(q):return q if isinstance(q,J) else J(q)
 def __add__(self,q):
  q=J.co(q);d=self.a.copy()
  for i,v in q.a.items():d[i]=d.get(i,0)+v
  return J(d)
 __radd__=__add__
 def __neg__(self):return J({i:-v for i,v in self.a.items()})
 def __sub__(self,q):return self+-J.co(q)
 def __rsub__(self,q):return J.co(q)+-self
 def __mul__(self,q):
  q=J.co(q);d={}
  for i,v in self.a.items():
   for j,w in q.a.items():
    ij=tuple(i[k]+j[k] for k in range(3))
    if sum(ij)<=ORDER:d[ij]=d.get(ij,0)+v*w
  return J(d)
 __rmul__=__mul__
 def inv(self):
  v=self.val();assert v!=0
  q=(self-v)*(1/v);out=J(1);term=J(1)
  for _ in range(ORDER):term*=(-q);out+=term
  return out*(1/v)
 def __truediv__(self,q):return self*J.co(q).inv()
 def __rtruediv__(self,q):return J.co(q)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  out=J(1)
  for _ in range(n):out*=self
  return out
 def power(self,n):
  n=s.Rational(n);v=self.val();unit=v**n;assert unit.is_Rational
  q=(self-v)*(1/v);out=J(1);term=J(1)
  for j in range(1,ORDER+1):term*=q;out+=s.binomial(n,j)*term
  return unit*out
 def der(self,k):
  d={}
  for i,v in self.a.items():
   if i[k]:ij=list(i);ij[k]-=1;d[tuple(ij)]=i[k]*v
  return J(d)
 def val(self):return self.a.get((0,0,0),s.Integer(0))

tj=J({(0,0,0):1,(1,0,0):1})
uj=J({(0,0,0):s.Rational(5,2),(0,1,0):1})
rj=J({(0,0,0):1,(0,0,1):1})
rhoj=(2*tj**3-1).power(s.Rational(1,2))
zj=(rj/rhoj).power(s.Rational(1,3))
kapj=4*tj**3/(rhoj*rhoj)
wj=-s.Rational(3,2)*((uj*uj-kapj*rj*rj)/s.Rational(9,4)).power(s.Rational(1,2))
hj=1+uj*uj-rj*rj+tj*rj/(2*rhoj)
cj=tj*zj*zj/3+zj*(uj+wj)/4
hsrcj=(1-uj/wj)/(108*rhoj)
betat=hj.der(0)-3*hj*cj.der(0)/(2*cj)
fj=hsrcj/betat
Rseed=fj.der(0)-fj*cj.der(0)/cj
checks['actual_sample_hsrc_WHOLE_twochannel']=hsrcj.val()==s.Rational(2,81)
checks['actual_sample_full_C_t_and_H_t']=cj.der(0).val()==-s.Rational(19,12) and hj.der(0).val()==-1
checks['actual_sample_full_source_seed_coefficient']=fj.val()==s.Rational(112,120123)

# Convert the derivatives to the ACTUAL CM product normals at fixed Q,b.
# y^2=23/4, h=3alpha/2 at this point.  No t-normal is dropped.
ys,aa,zz=s.symbols('ys alpha_s zeta_s')
hs=3*aa/2
Uy=(40*ys+3)/91
ry=(10+12*ys)/91
UP=ry/2
RP=(Uy-1)/2
UQ=3*hs*hs*Uy/2
RQ=3*hs*hs*ry/2
CUv=cj.der(1).val();CRv=cj.der(2).val()
CPv=cj.der(0).val()+UP*CUv+RP*CRv
CQv=UQ*CUv+RQ*CRv
HQv=3*hs*hs*ys
R0=Rseed.val();Rt=Rseed.der(0).val();RU=Rseed.der(1).val();RR=Rseed.der(2).val()
RPseed=Rt+UP*RU+RP*RR
RQseed=UQ*RU+RQ*RR
mv=-3*hs*hs*ys*R0/2
mPv=-3*hs*hs*ys*(2*R0+RPseed)/2
mQv=-s.Rational(3,2)*((2*hs*ys*ys+s.Rational(3,2)*hs**4)*R0+hs*hs*ys*RQseed)
kpv=4*aa*(ys+1)*(3-2*zz)/19
kqv=2*(ys+1)*(9*zz-4)/19
def sample_reduce(q):
 q=s.expand(q)
 for v,rel in [(ys,ys*ys-s.Rational(23,4)),(zz,zz*zz+zz+1),(aa,aa**3-2)]:q=s.rem(q,rel,v)
 return s.factor(q)
checks['actual_spinor_FULL_volume_unit']=sample_reduce(s.Rational(5,2)*Uy-s.Rational(3,4)*ry-ys)==0
A0v=sample_reduce(mQv*kpv-mPv*kqv)
AHv=sample_reduce(mv*kpv*HQv)
ACv=sample_reduce(mv*(kpv*CQv-kqv*CPv))
nv={H:s.Rational(27,4),C:s.Rational(7,12)}
samplecompact=(A0v*s.Matrix([1,0,0,0])+AHv*MH[:,0].subs(nv)+ACv*MC[:,0].subs(nv)).applyfunc(sample_reduce)
skweight=sample_reduce(AHv-3*nv[H]*ACv/(2*nv[C]))
checks['WHOLE_CM_repair_actual_secondkind_remainder_NONZERO']=skweight!=0 and samplecompact[2]!=0 and samplecompact[3]!=0
checks['WHOLE_CM_repair_actual_remainder_NOT_ZERO']=any(q!=0 for q in samplecompact)
checks['actual_seed_and_projector_denominators_nonzero']=all(q!=0 for q in [betat.val(),cj.val(),R0])
assert all(checks.values()),checks

out={
 'status':'INDEPENDENT_FULL_LITERAL_T_SEED_PLUS_ACTUAL_CM_PROJECTOR_CURRENT_PASS_WITH_NONZERO_ALL4_REMAINDER_NOT_CLOSURE',
 'authoritative_candidate':'source-incidence-correspondence/actual_CM_projector_source_seed.py/json',
 'checks':checks,'check_count':len(checks),
 'FULL_original_source':'beta_original=hsrc*dt*dU*dR*thetaH,hsrc=−(U/W−1)/(108rho). The entire physical two-channel source factor is retained.',
 'ONE_literal_current':{
  'seed':'Jt=f*dU*dR*omega0−f*Ct*p*dt*dU*dR/(2C Z),f=hsrc/[Ht−3H Ct/(2C)]',
  'Rseed':'partial_t|U,R(f)−f*Ct/C, every physical rho,z,kappa,W normal included',
  'CM':'JCM=m*KP*dlogb*omega0,m=−3rho*h²*y*Rseed/(2t)',
  'KP':'kP*eta+kQ*omegaQ,kP=2zeta*t*(y+rho)/[(h−alpha*t)(zeta*h−alpha*t)],kQ=2(y+rho)(alpha*t+zeta²h)/[alpha²(h−alpha*t)(zeta*h−alpha*t)]',
  'normalization':'alpha³=2,zeta²+zeta+1=0,h³=H,y²=H−1;eta=dt/rho,omegaQ=dh/y;dKP=t*eta*omegaQ',
 },
 'EXACT_WHOLE_LITERAL_REMAINDER':{
  'identity':'beta_original=d(Jt+JCM)+eta*omegaQ*dlogb*(A0*omega0+AH*thetaH+AC*thetaC)',
  'A0':'mQ*kP−mP*kQ',
  'AH':'m*kP*HQ',
  'AC':'m*(kP*CQ−kQ*CP)',
  'normals':'DP t=rho,DP rho=3t²,DP holds Q,b; DQ h=y,DQ y=3h²/2,DQ holds P,b. HP=0,HQ=3h²y. CP,CQ and mP,mQ retain every actual spinor and rho,z,W motion.',
  'source_volume':'dt*dU*dR=(3rho*h²*y/2)*eta*omegaQ*dlogb; the source-cancelling mt term is exactly −Rseed*dt*dU*dR.',
 },
 'EXACT_ALL4_AND_FIBER_RECEIPT':{
  'compact_vector':'A0*e0+AH*MH[:,0]+AC*MC[:,0] in basis j=0,1,3,4',
  'fiber_primitive':'S=(AH*polyH+AC*polyC)/Z',
  'polyH':str(polyH),'polyC':str(polyC),
  'identity':'A0*omega0+AH*thetaH+AC*thetaC=compact_vector*omega_basis+d_p S',
  'optional_literal_fiber_current':'Adding −eta*omegaQ*dlogb*S to Jt+JCM serves the entire d_pS term and leaves precisely the four compact rows, with no discarded cochain.',
  'SK_weight':'AH−3H*AC/(2C); SK vector=SK_weight*(72C³,−96C⁴/H)/Delta,Delta=4C⁶−729H⁴',
 },
 'actual_sample':{
  'physical_point':'t=rho=R=z=1,U=5/2,W=−3/2,H=27/4,C=7/12; CM h=3alpha/2,y²=23/4,b=13/(4y−1)',
  'hsrc':str(hsrcj.val()),'Ht':str(hj.der(0).val()),'Ct':str(cj.der(0).val()),'f':str(fj.val()),
  'Rseed':str(R0),'Rseed_t':str(Rt),'Rseed_U':str(RU),'Rseed_R':str(RR),
  'sample_KP_coefficients':'kP=4alpha*(y+1)*(3−2zeta)/19,kQ=2*(y+1)*(9zeta−4)/19',
  'A0':str(A0v),'AH':str(AHv),'AC':str(ACv),
  'SK_weight':str(skweight),'remaining_j0_j1_j3_j4':[str(q) for q in samplecompact],
  'nonzero_proof':'Each displayed sample coefficient is reduced in the exact basis alpha^i*zeta^j*y^k, i<3,j<2,k<2. The nonzero SK weight and both SK rows are exact algebraic nonzero values, not numerical guesses.',
 },
 'retained_counterdivisors':['Ht−3H Ct/(2C)=0','h−alpha*t=0','zeta*h−alpha*t=0','rho=0,y=0','b=0,infinity','y−d=0 and y+d=0','C=0,Z=0','R=0,W=0','CM infinity and all intersections'],
 'limitations':'The whole source cancellation of the seed scalar Rseed is genuine, and all actual P,Q normals and endpoint cochains were included. The full resulting compact remainder is nonzero at an actual point; this concrete candidate is a partial current, not a primitive or certificate. No exclusion of other t-moving currents is inferred.',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'WHOLE full-source t-seed + actual CM projector; all4/fiber receipt and exact NONZERO SK remainder')
