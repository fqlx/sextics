"""WHOLE original-field Y-seed + PLUS CMdesc packet, independent full audit.

No alpha,zeta,h,y,rho auxiliary radical appears in the actual current.
Every amplitude derivative and endpoint fiber term is retained.
"""
from pathlib import Path
import json,ast
import sympy as s

t,U,z,W,H,C,p,Z,rho=s.symbols('t U z W H C p Z rho',nonzero=True)
g=2*t**3-1
Hphys=1+U*U-g*z**6+t*z**3/2
Cphys=t*z*z/3+z*(U+W)/4
DU=lambda q:s.diff(q,U)+U*s.diff(q,W)/W
DT=lambda q:s.diff(q,t)-6*t*t*z**6*s.diff(q,W)/W
DZ=lambda q:s.diff(q,z)-12*t**3*z**5*s.diff(q,W)/W
der=[DT,DU,DZ]
Y=lambda q:DT(q)+3*U*DU(q)/(4*t)-z*DZ(q)/(4*t)
def physical_zero(q):
 n=s.together(q).as_numer_denom()[0]
 return s.factor(s.rem(n,W*W-U*U+4*t**3*z**6,W))==0
B=U/W-1
A=3*(U*U-1)-3*(2*t**3+3)*z**6-t*z**3
Ppoly=-12*U*U-6+(24*t**3-72)*z**6-t*z**3
fY=-t*B/(27*A)
RY=-B*Ppoly/(108*A*A)
checks={
 'FULL_original_source_ratio_Y_invariant':physical_zero(Y(B)),
 'actual_Y_C_weight':physical_zero(Y(Cphys)-Cphys/(2*t)),
 'actual_Y_H_defect':physical_zero(4*t*Y(Hphys)-3*Hphys-A),
 'actual_Yseed_WHOLE_scalar_remainder':physical_zero(Y(fY)-fY/(2*t)-RY),
 'actual_mu_Y_divergence':s.factor(DT(3*z*z)+DU(3*z*z*3*U/(4*t))+DZ(-3*z**3/(4*t)))==0,
}

# Explicit rational twoform eta*psi and oneform rho*psi in (t,U,z).
S=g*z**3-t/4
Q=S*S-g*U*U
etaPsi=[2*S/Q,-6*U*g*z*z/Q,s.Integer(0)] # tU,tz,Uz
rhoPsi=[-2*U*(3*t*t*g*z**3+(t**3+1)/4)/Q,2*g*S/Q,-6*U*g*g*z*z/Q]
rr=rho*z**3-t/(4*rho)
rt=3*t*t*z**3/rho+(t**3+1)/(4*rho**3)
K=rr*rr-U*U
def rho_zero(q):
 n=s.together(q).as_numer_denom()[0]
 return s.factor(s.rem(n,rho*rho-g,rho))==0
checks['original_rational_eta_psi_tU']=rho_zero(etaPsi[0]-2*rr/(rho*K))
checks['original_rational_eta_psi_tz']=rho_zero(etaPsi[1]+6*U*z*z/K)
checks['original_rational_rho_psi_t']=rho_zero(rhoPsi[0]+2*rho*U*rt/K)
checks['original_rational_rho_psi_U']=rho_zero(rhoPsi[1]-2*rho*rr/K)
checks['original_rational_rho_psi_z']=rho_zero(rhoPsi[2]+6*U*rho*rho*z*z/K)

# Literal endpoint differentiation of the entire Yseed, including base3 term.
L=H+C*p;ff=L*L-4*p**6
thetaH=-L/Z**3;thetaC=-p*L/Z**3
Dp=lambda q:s.diff(q,p)+s.diff(q,Z)*(C*L-12*p**5)/Z
fy,fyY,aa=s.symbols('fy fyY aa')
YH=(aa+3*H)/(4*t)
literal_seed=(fyY/Z+fy*(YH*thetaH+C*thetaC/(2*t))+fy*Dp(p/Z)/(4*t))
want=fy*aa*thetaH/(4*t)+(fyY-fy/(2*t))/Z
num=s.together(literal_seed-want).as_numer_denom()[0]
checks['literal_Yseed_base3_fiber_cochain_ALL_normals']=s.factor(s.rem(num,Z*Z-ff,Z))==0

# Exact physical jets only evaluate this ONE fixed full rational packet.
# Reuse the audited three-variable arithmetic class, without executing any
# prior candidate or its tests.  Variables are now (t,U,z), NOT (t,U,R).
helper=Path(__file__).with_name('actual_full_t_seed_CM_projector_literal_audit.py')
node=next(n for n in ast.parse(helper.read_text()).body if isinstance(n,ast.ClassDef) and n.name=='J')
env={'s':s,'ORDER':3}
exec(compile(ast.Module(body=[node],type_ignores=[]),str(helper),'exec'),env)
J=env['J']
tj=J({(0,0,0):1,(1,0,0):1})
uj=J({(0,0,0):s.Rational(5,2),(0,1,0):1})
zj=J({(0,0,0):1,(0,0,1):1})
wj=-s.Rational(3,2)*((uj*uj-4*tj**3*zj**6)/s.Rational(9,4)).power(s.Rational(1,2))
gj=2*tj**3-1
hj=1+uj*uj-gj*zj**6+tj*zj**3/2
cj=tj*zj*zj/3+zj*(uj+wj)/4
bj=uj/wj-1
aj=3*(uj*uj-1)-3*(2*tj**3+3)*zj**6-tj*zj**3
pj=-12*uj*uj-6+(24*tj**3-72)*zj**6-tj*zj**3
ryj=-bj*pj/(108*aj*aj)
sj=gj*zj**3-tj/4
qj=sj*sj-gj*uj*uj
epj=[2*sj/qj,-6*uj*gj*zj*zj/qj,J(0)]
rpj=[-2*uj*(3*tj*tj*gj*zj**3+(tj**3+1)/4)/qj,2*gj*sj/qj,-6*uj*gj*gj*zj*zj/qj]
N=bj*pj/(72*tj*aj*aj*(hj-2*tj**3))
hgrad=[hj.der(i) for i in range(3)]
cgrad=[cj.der(i) for i in range(3)]
hpsi=[hgrad[0]*rpj[1]-hgrad[1]*rpj[0],
      hgrad[0]*rpj[2]-hgrad[2]*rpj[0],
      hgrad[1]*rpj[2]-hgrad[2]*rpj[1]]
qcm=[N*(tj*hj*(hj-1)*epj[i]-tj*tj*hpsi[i]/3) for i in range(3)]
V=[qcm[2],-qcm[1],qcm[0]] # iV(dt*dU*dz)=Vt*dUdz−VU*dtdz+Vz*dtdU
divV=sum(V[i].der(i) for i in range(3))
VH=sum(V[i]*hgrad[i] for i in range(3))
VC=sum(V[i]*cgrad[i] for i in range(3))
E0=3*zj*zj*ryj+divV
vals={'RY':ryj.val(),'N':N.val(),'divV':divV.val(),
      'E0':E0.val(),'EH':VH.val(),'EC':VC.val()}
checks['actual_FULL_source_Yseed_RY']=vals['RY']==-s.Rational(4160,81)
checks['WHOLE_CMdesc_amplitude_AND_rational_forms_E0']=vals['E0']/3==-s.Rational(7458155552,180063)
checks['WHOLE_CMdesc_actual_H_normal']=vals['EH']/3==-s.Rational(47840,19)
checks['WHOLE_CMdesc_actual_C_normal']=vals['EC']/3==-s.Rational(2382320,96957)
scalarH=vals['EH']-3*hj.val()*vals['EC']/(2*cj.val())
scalar0=vals['E0']-vals['EC']/cj.val()
checks['WHOLE_scalarized_thetaH_and_omega0_match']=scalarH/3==-s.Rational(5841320,2793) and scalar0/3==-s.Rational(365077980128,8823087)

# Native all4 projection, retaining an explicit literal rational fiber kernel.
conn=json.loads((Path(__file__).parents[1]/'native_q_connection.json').read_text())
MH=s.Matrix([[s.sympify(q,locals={'H':H,'C':C}) for q in row] for row in conn['H']])
MC=s.Matrix([[s.sympify(q,locals={'H':H,'C':C}) for q in row] for row in conn['C']])
Delta=4*C**6-729*H**4
polyH=(-12*C**6*p-8*C**5*H+48*C**4*p**5-72*C**3*H*p**4+108*C**2*H**2*p**3-162*C*H**3*p**2+243*H**4*p)/(H*Delta)
polyC=(16*C**5*p+12*C**4*H-72*C**3*p**5+108*C**2*H*p**4-162*C*H**2*p**3+243*H**3*p**2)/Delta
ex0,exH,exC=s.symbols('ex0 exH exC')
compact=ex0*s.Matrix([1,0,0,0])+exH*MH[:,0]+exC*MC[:,0]
literal=ex0/Z+exH*thetaH+exC*thetaC
bas=s.Matrix([1,p,p**3,p**4])
num=s.together(literal-bas.dot(compact)/Z-Dp((exH*polyH+exC*polyC)/Z)).as_numer_denom()[0]
checks['WHOLE_native_ALL4_AND_entire_fiber_primitive']=s.factor(s.rem(num,Z*Z-ff,Z))==0
nv={H:hj.val(),C:cj.val(),ex0:vals['E0'],exH:vals['EH'],exC:vals['EC']}
sample_excess=compact.subs(nv).applyfunc(s.factor)
checks['WHOLE_actual_remaining_secondkind_rows_NONZERO']=sample_excess[2]!=0 and sample_excess[3]!=0
checks['WHOLE_actual_current_is_NOT_primitive']=any(q!=0 for q in sample_excess)
assert all(checks.values()),checks

out={
 'status':'INDEPENDENT_WHOLE_ORIGINAL_FIELD_Y_PLUS_CMdesc_PACKET_PASS_WITH_NONZERO_ALL4_REMAINDER_NOT_CLOSURE',
 'authoritative_input':'source-incidence-correspondence/actual_full_CM_repair_descent.py/json; root_Y_CMdesc_full_point.py/json',
 'checks':checks,'check_count':len(checks),
 'ORIGINAL_field':'t,U,z,W; W²=U²−4t³z⁶;H=1+U²−(2t³−1)z⁶+t z³/2;C=t z²/3+z(U+W)/4;Z²=(H+Cp)²−4p⁶. No auxiliary CM radical remains.',
 'physical_derivations':'Dt=partial_t−6t²z⁶ partial_W/W;DU=partial_U+U partial_W/W;Dz=partial_z−12t³z⁵ partial_W/W, acting on the actual field',
 'actual_full_source':'beta_original=−B*z²*dt*dU*dz*thetaH/36; B=U/W−1; entire twochannel factor retained',
 'ONE_original_field_current':{
  'mu':'3z²*dt*dU*dz',
  'Y':'partial_t+(3U/(4t))*partial_U−z*partial_z/(4t), with every W normal included',
  'A':'3(U²−1)−3(2t³+3)z⁶−t z³',
  'Ppoly':'−12U²−6+(24t³−72)z⁶−t z³',
  'fY':'−tB/(27A)',
  'JY':'fY*iY(mu)*omega0−mu*fY*p/(4tZ)',
  'RY':'−B*Ppoly/(108A²), dJY=beta_original+mu*RY*omega0',
  'JCMdesc_PLUS':'QCM*omega0;QCM=N*[tH(H−1)*(eta wedge psi)−(t²/3)*dH wedge (rho*psi)]',
  'N':'B*Ppoly/[72tA²(H−2t³)]',
  'rational_forms':'g=2t³−1,S=gz³−t/4,Q=S²−gU²;eta*psi=2dt*(S dU−3Ug z²dz)/Q;rho*psi=2[gS dU−U(3t²g z³+(t³+1)/4)dt−3Ug²z²dz]/Q',
 },
 'EXACT_WHOLE_literal_identity':{
  'definition':'QCM=iVCM(dt*dU*dz),E0=3z²RY+div(VCM),EH=VCM(H),EC=VCM(C)',
  'identity':'beta_original=d(JY+JCMdesc)−dt*dU*dz*(E0*omega0+EH*thetaH+EC*thetaC)',
  'sign':'The exported point E coefficients are d(current)−beta_original. The actual residual beta_original−d(current) is their NEGATIVE.',
  'all_normals':'divVCM differentiates the entire rational N, every H,t factor and every component of eta*psi,rho*psi, including the dt leg of rho*psi. No separate/unweighted trace or frozen normal enters.',
 },
 'EXACT_ALL4_AND_FIBER':{
  'excess_vector':'E0*e0+EH*MH[:,0]+EC*MC[:,0],basis j0,1,3,4',
  'excess_fiber_primitive':'(EH*polyH+EC*polyC)/Z',
  'polyH':str(polyH),'polyC':str(polyC),
  'literal_receipt':'E0*omega0+EH*thetaH+EC*thetaC=excess_vector*omega_basis+d_p(excess_fiber_primitive)',
  'source_fiber_sign':'For beta=dJ−vol*(excess+dpS), adding +vol*S to J serves the entire negative dpS source residual and leaves precisely −vol*excess_vector. No cochain is dropped.',
 },
 'actual_exact_sample':{
  'point':'t=z=1,U=5/2,W=−3/2,H=27/4,C=7/12,A=−1/4',
  'density_convention':'E0,EH,EC below multiply dt*dU*dz; root point exports coefficients multiplying mu=eta*dU*dR=3z²*dt*dU*dz. At this point the former are exactly3 times the latter.',
  **{k:str(q) for k,q in vals.items()},
  'VCM_t_U_z':[str(q.val()) for q in V],
  'scalarized_thetaH_excess':str(scalarH),'scalarized_omega0_excess':str(scalar0),
  'root_mu_normalized_E0_EH_EC':[str(vals[k]/3) for k in ['E0','EH','EC']],
  'root_mu_normalized_scalarH_scalar0':[str(scalarH/3),str(scalar0/3)],
  'excess_native_rows_j0_j1_j3_j4':[str(q) for q in sample_excess],
  'actual_source_residual_native_rows':[str(-q) for q in sample_excess],
 },
 'retained_counterdivisors':['A=0','H−2t³=0','Q=0 source K support','t=0','W=0','Z=0 and endpoint infinity','all chart boundaries and collisions'],
 'conclusion':'This is a fully rational original-field source-bound two-piece current with all normals/cochains included. Its exact j3,j4 and full compact remainder are nonzero at the actual source point. The candidate is partial; no global nonexistence claim follows.',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'WHOLE original-field Yseed+PLUS CMdesc; exact all4/fiber audit and root point values matched')
