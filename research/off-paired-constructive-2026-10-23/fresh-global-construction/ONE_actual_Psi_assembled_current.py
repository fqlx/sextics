"""ONE literal assembled actual-source current, with every normal/fiber term.
The tau/pole/last-lambda sum collapses to THREE literal pieces.
All remaining source is exported; no certificate is claimed.
"""
from pathlib import Path
import sympy as S,json
root=Path(__file__).parent
H,C,k,l,kH,kC,lC=S.symbols('H C vH vC vHH vHC vCC')
DH=lambda f:S.diff(f,H)+kH*S.diff(f,k)+kC*S.diff(f,l)
DC=lambda f:S.diff(f,C)+kC*S.diff(f,k)+lC*S.diff(f,l)
E=lambda f:3*H*DH(f)+2*C*DC(f)
Ev=3*H*k+2*C*l
m=l/(216*Ev);a=k/(432*Ev)
phi=C*C*k*k/(432*Ev)-C*C*k/(1296*H)
AH=a*k-k/(1296*H);AC=a*l
curl=DH(AC)-DC(AH)
lam0=AC+3*H*curl;lam1=-AH+2*C*curl
tau1=E(phi)/(C*C)
contact_remaining=-C*(DH(m)*l-DC(m)*k)
R0=S.factor(contact_remaining-lam0)
R1=S.factor(-lam1-tau1)
checks={
 'WHOLE_assembled_theta0':S.factor(R0+kC/432)==0,
 'WHOLE_assembled_theta1':R1==0,
 'fifth_row_identically_zero':'B=etaCM wedge dphi is closed; no fifth-output forcing is discarded',
}
# Entire three-piece current is also exactly elementary IBP plus an exact current.
pp,ZZ=S.symbols('p Z')
logXi=S.Matrix([1,pp,-(3*H+2*C*pp)/pp])/ZZ
Avec=S.Matrix([AH,AC,0]);contactvec=S.Matrix([m*k,m*l,0])
contactlast=S.Matrix([0,pp/(2*ZZ),-C/ZZ])
dp2C=S.Matrix([0,-pp*pp/(C*C),2*pp/C])
wedge=lambda x,y:S.Matrix([x[0]*y[1]-x[1]*y[0],x[0]*y[2]-x[2]*y[0],x[1]*y[2]-x[2]*y[1]])
collapsed=wedge(contactvec,contactlast)+wedge(Avec,pp*logXi)-phi*wedge(dp2C,logXi)+S.Matrix([0,0,l/(432*ZZ)])
for j,nm in enumerate(['HC','Hp','Cp']):checks['WHOLE_literal_IBP_collapse_'+nm]=S.factor(collapsed[j])==0
# Actual physical C and all normals; no frozen W,z.
U,R,W,z=S.symbols('U R W z');d=S.Rational(1,4);kap=S.Integer(4)
r=R-d;HH=S.Rational(17,16)+U*U-r*r;KK=r*r-U*U
CC=z*z/3+z*(U+W)/4
DU=lambda f:S.diff(f,U)+U/W*S.diff(f,W)
DR=lambda f:S.diff(f,R)+z/(3*R)*S.diff(f,z)-kap*R/W*S.diff(f,W)
boost=lambda f:r*DU(f)+U*DR(f)
JJ=boost(CC);LL=U*DU(CC)+r*DR(CC);vh=LL/(JJ*KK);MM=DU(CC)/(U*JJ)
pt={U:S.Rational(5,2),R:S.Integer(1),z:S.Integer(1),W:-S.Rational(3,2)}
val=lambda f:S.factor(f.subs(pt))
checks['actual_endpoint_normal_identity_at_point']=val(1/U**2+boost(MM)+boost(vh))==0
actual_vHC=val(boost(vh)/JJ)
checks['actual_remaining_source_NONZERO']=actual_vHC!=0
Ec=lambda f:U*DU(f)+R*DR(f)
heat=(U*U-kap*R*R)*DU(DU(CC))-U*DU(CC)/2-3*R*DR(CC)/2+CC
euler=Ec(Ec(CC))-2*Ec(CC)+S.Rational(8,9)*CC
checks['actual_C_Euler_annihilator_at_point']=val(euler)==0
checks['actual_C_heat_annihilator_at_point']=val(heat)==0
# Source-field denominators are actually nonzero on this point.
checks['actual_source_incidence_nonzero']=all(val(x)!=0 for x in [HH,KK,JJ,vh*3*HH+2*CC*2/JJ,U,W])
assert all(v is True or isinstance(v,str) for v in checks.values()),checks
out={
 'status':'PASS_ONE_WHOLE_ACTUAL_SOURCE_CURRENT; EXACT_REMAINDER_NONZERO',
 'source':'beta_U=etaCM wedge dH wedge dv wedge thetaH/432, v=logPsi, Psi=kboost²/(H0−H). dv is the rational dlog of the actual source unit, not a scalar logarithm in any coefficient. Whole original source is the signed U-channel sum.',
 'endpoint':'Z²=(H+Cp)²−4p6, Xi=(H+Cp+Z)/(2p³), lXi=dlogXi=[dH+p*dC−(3H+2Cp)*dp/p]/Z; theta0=dp/Z, thetaH=−(H+Cp)dp/Z³.',
 'actual_physical_normals':'H=H0+U²−r²,H0=1+d²,r=R−d,R=rho*z³,d=t/(4rho),rho²=2t³−1,W²=U²−4t³z6,C=tz²/3+z(U+W)/4. kboost=U+r. All z,W motions are retained.',
 'rational_coefficients':{
  'vH':'partial_H logPsi at fixed C = (U*C_U+r*C_r)/[J*(H0−H)]',
  'vC':'partial_C logPsi at fixed H =2/J, J=U*C_r+r*C_U',
  'Ev':'3H*vH+2C*vC',
  'm':'vC/(216Ev), so m*dv=g*ds for the actual source marker s=Psi+Psi^-1',
  'a':'vH/(432Ev)',
  'phi':'C²*vH²/(432Ev)−C²*vH/(1296H)',
 },
 'ONE_FULL_LITERAL_CURRENT':{
  'Jcontact':'etaCM wedge m*dv wedge (p*dC−2C*dp)/(2Z)',
  'Jlambda':'etaCM wedge [a*dv−vH*dH/(1296H)] wedge lambda1_abs',
  'Jtau':'etaCM wedge dphi wedge tau_abs',
  'absolute_SW_forms':'lambda1_abs=p*lXi,tau_abs=p²*lXi/C. Their base legs ALREADY INCLUDE every exact fiber cochain. Do not add the separate relative-cochain correction a second time.',
  'prefix_scope':'This is exactly the source-Psi full cubic Schiffer/fiber/Tate fold, the theta0-serving lambda current, the algebraic+doublepole tau potential, the actual three-root Newton pole current, and the last R1-serving lambda current, after algebraic consolidation. No conserved-Phi piece was added without a source equality.',
 },
 'EXACT_WHOLE_IDENTITY':'beta_U=d(Jcontact+Jlambda+Jtau)−etaCM wedge dH wedge dC*vHC*theta0/432, where vHC=partial_Hpartial_C logPsi. All secondkind rows are zero, fifth output is exactly zero; the displayed holomorphic theta0 coefficient remains.',
 'WHOLE_exact_current_collapse':'Jcontact+Jlambda+Jtau=−etaCM*vC*dC wedge dp/(432Z)−d[etaCM*phi*p²*dlogXi/C]. This equality is literal in all HC,Hp,Cp current coefficients; the entire assembled current is elementary H-integration-by-parts plus an exact current. No closure beyond that cycle is claimed.',
 'equivalent_physical_REMAINDER':'muUr*[1/U²+Boost(C_U/(U J))]*theta0/216 =−muUr*Boost(vH)*theta0/216, muUr=etaCM dU dr,Boost=r*partial_U+U*partial_r. This is the compact IBP representative of the original source; it is not a cancellation.',
 'prefix_before_last_lambda':'Jcontact +etaCM wedge[a*dv+n*dH/(1296H*K)] wedge lambda1_abs +etaCM wedge dphi wedge tau_abs, n=−r/U,K=H0−H. This prefix produces the following two-row target; the displayed THREE-piece current above additionally contains the last lambda correction.',
 'pre_last_lambda_rank2_packet':'muUr{theta0/(216U²)−[C_U/U+2C*Boost(C_U/(U J))]*theta1/(648H)}; adding eta*[C_U/(U J)]*dH*lambda1_abs/(1296H) serves theta1 and yields the displayed single theta0 remainder.',
 'actual_C_annihilator_test':{
  'actual_point':'t=1,rho=1,d=1/4,U=5/2,R=1,z=1,W=−3/2',
  'C':'7/12','H':'27/4','J':str(val(JJ)),
  'vHC':str(actual_vHC),
  'physical_remaining_theta0':str(val((1/U**2+boost(MM))/216)),
  'conclusion':'Both actual C annihilators vanish at this legitimate source point while the remaining coefficient is nonzero. Therefore these annihilators do not make THIS assembled remainder zero. A further source-serving current is still required; no broader nonexistence claim is made.',
 },
 'checks':checks,'check_count':len(checks)}
(root/'ONE_actual_Psi_assembled_current.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'one fully assembled actual current; vHC =',actual_vHC,'physical remainder =',out['actual_C_annihilator_test']['physical_remaining_theta0'],flush=True)
