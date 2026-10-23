"""Literal mixed Euler homotopy for a background infinity-row source.

It transfers the source to explicit derivatives of the endpoint coefficient.
Those derivatives are retained; their cancellation is not asserted.
"""
import json
from pathlib import Path
import sympy as S

D,B,q,w,H,z=S.symbols('D B q w H z',nonzero=True)
Delta=4*B**6-729*D**4
lam=(-2*B)**6/(768*Delta)
f=(D+B*q)**2-4*q**6
def E(f):return 3*D*S.diff(f,D)+2*B*S.diff(f,B)
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
check('lambda-weight-zero',E(lam))
check('actual-parameter-divergence',S.diff(3*D*lam/5,D)+S.diff(2*B*lam/5,B)-lam)
# Clear w^3 in E(q^2/w)+d_q(q^3/w)=0 using w^2=f.
check('literal-background-infinity-Euler',
      -q*q*(D+B*q)*(3*D+2*B*q)+3*q*q*f-q**3*S.diff(f,q)/2)
# The same step applies to the complete homogeneous background five-row
# numerator from the actual Prym mixed source, not only its omega2 row.
zz=-2*B
Prows=[3*D**2*zz**4/(128*Delta),-D*zz**5/(256*Delta),
       zz**6/(768*Delta),-81*D**3*zz/(16*Delta),-27*D**2*zz**2/(16*Delta)]
P4=sum(a*q**j for j,a in enumerate(Prows))
check('actual-full-P4-homogeneous-two',E(P4)+q*S.diff(P4,q)-2*P4)
rat=zz**4*(3*D+q*zz)/(128*Delta)
check('actual-rational-background-one-form-weight-zero',E(rat)+q*S.diff(rat,q)+rat)

ZH,hh,u,v=S.symbols('Z h u v',nonzero=True)
a=S.symbols('a')
Hactual=1+ZH**-2+hh**6
Cactual=q/3+z*a/2
HE=3*(H-1-z**6)+12*z**6
CE=q/3+7*z*a/4
check('endpoint-H-Euler-defect',HE-3*H-(9*z**6-3))
check('endpoint-C-Euler-defect',CE-2*Cactual-(-q/3+3*z*a/4))
# Background parameter field expressed in H,z has divergence five.
check('physical-H-z-divergence',S.diff(HE,H)+S.diff(2*z,z)-5)

p,C,Zp=S.symbols('p C Zp',nonzero=True)
S0=H+C*p
fep=S0*S0-4*p**6
vc=-S0*p/Zp**3
FE=-S0*p*p/Zp**3 # partial_C(p/Zp)
def endpointE(f):
    return 3*H*S.diff(f,H)+2*C*S.diff(f,C)+S0*(3*H+2*C*p)*S.diff(f,Zp)/Zp
def dp(f):return S.diff(f,p)+(S0*C-12*p**5)*S.diff(f,Zp)/Zp
num=S.fraction(S.cancel(endpointE(vc)+4*vc+dp(FE)))[0]
num=S.rem(S.Poly(num,Zp),S.Poly(Zp*Zp-fep,Zp)).as_expr()
check('literal-endpoint-C-column-Euler',num)

# Formal exterior coefficient verification.  Put vol=dH^dz and order the
# temporary top frame as v^Omega2^vol, the negative of the original frame.
# Y=lambda*E/5, t=q^3/w, t*dq=q*Omega2.
x,y,tq,ve,vq,v0,omega,tau=S.symbols('lambda0 divY tq ve vq v0 omega tau')
source=-x*v0*omega
dJY=-y*v0*omega-x*ve*omega/5+x*v0*tq/5
dK=-x*v0*tq/5-x*tau*vq/5
assert S.expand((source-dJY-dK-x*(ve+q*vq)*omega/5).subs({y:x,tau:q*omega}))==0
checks.append('parameter-and-q-current-full-product-rule')

data={
 'status':'Actual mixed infinity Euler current with explicit endpoint-derivative defect; no closure',
 'constant_scope':'fixed characteristic-zero k; k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'background':{'w2':str(f),'Delta':str(Delta),'lambda':str(lam)},
 'parameter_field':'E=3D*dD+2B*dB=(3H-3+9z^6)*dH+2z*dz; div E=5',
 'background_Euler':'nabla_E Omega2=-d_q(q^3/w)',
 'source':'T=lambda*v_endpoint ^ dH ^ Omega2 ^ dz',
 'first_current':'JY=-v_endpoint ^ Omega2 ^ i_(lambda*E/5)(dH^dz)',
 'q_current':'K=(lambda/5)*(q^3/w)*v_endpoint ^ dH ^ dz',
 'full_transfer':'T=d(JY+K)-(lambda/5)*(nabla_E v_endpoint+q*nabla_q v_endpoint)^dH^Omega2^dz',
 'complete_background_variant':{
    'actual_P4':str(P4),'actual_rational_coefficient':str(rat),
    'condition':'alpha=R(q,D,B)dq has total background weight zero: nabla_E alpha=-d_q(qR)',
    'source':'T=v_endpoint^dH^alpha^dz',
    'currents':'J=-(1/5)*v_endpoint^alpha^i_E(dH^dz); K=(qR/5)*v_endpoint^dH^dz',
    'full_transfer':'T=d(J+K)-(1/5)*(nabla_E v_endpoint+q*nabla_q v_endpoint)^dH^alpha^dz',
    'warning':'Every actual P4 row, including omega1 and omega4, has total background weight zero after its coefficient is included. No row-only resonance assumption is used.'},
 'physical_total_Euler':{'Hdot':str(HE),'Cdot':str(CE)},
 'endpoint_C_specialization':{
    'v':'v_endpoint=partial_C omega0',
    'Euler_weight':'nabla_(3H*dH+2C*dC) v=-4v-d_p F, F=partial_C(p/Zp)=-(H+Cp)*p^2/Zp^3',
    'defect':'(9z^6-3)*partial_H v+(-q/3+3za/4)*partial_C v',
    'finite_homotopy':'T=d[5(JY+K)+lambda*F*dH^Omega2^dz]-lambda*defect^dH^Omega2^dz',
    'warning':'The defect is not zero. This does not eliminate the background infinity component without a further coupled endpoint correction.'},
}
Path(__file__).with_name('infinity-euler-transfer-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact mixed infinity Euler and literal endpoint-defect checks')
