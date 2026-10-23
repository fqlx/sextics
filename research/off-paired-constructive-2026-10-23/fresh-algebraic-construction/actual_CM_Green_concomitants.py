"""Two literal finite Green concomitants for the full physical C branch.

Full t-normal correction coefficients and the actual source Psi pairing are
retained.  These are constructive currents, not the missing two-row solution.
"""
from pathlib import Path
import json
import sympy as S

U,R,z,W,t,rho,kap=S.symbols('U R z W t rho kappa',nonzero=True)
A=t*z*z/3;C=A+z*(U+W)/4;SS=U+W
DU=lambda f:S.diff(f,U)+U/W*S.diff(f,W)
DR=lambda f:S.diff(f,R)+z/(3*R)*S.diff(f,z)-kap*R/W*S.diff(f,W)
DT=lambda f:(S.diff(f,t)+3*t*t/rho*S.diff(f,rho)-t*t*z/rho**2*S.diff(f,z)
             -3*kap/(t*rho**2)*S.diff(f,kap)+3*kap*R*R/(2*t*rho**2*W)*S.diff(f,W))
E0=lambda f:U*DU(f)+R*DR(f)
def red(f):
    n,d=S.cancel(f).as_numer_denom()
    return S.factor(S.rem(n,W*W-U*U+kap*R*R,W))
checks={}
def ck(name,f):
    checks[name]=red(f)==0
    assert checks[name],(name,red(f))

LC=lambda f:W*W*DU(DU(f))-U*DU(f)/2-3*R*DR(f)/2+f
Lstar=lambda f:W*W*DU(DU(f))+S.Rational(9,2)*U*DU(f)+S.Rational(3,2)*R*DR(f)+5*f
ck('PHYSICAL_C_PDE1',E0(E0(C))-2*E0(C)+S.Rational(8,9)*C)
ck('PHYSICAL_C_PDE2',LC(C))
phis=[1/(R**3*z),1/(R*z*z*W)]
for j,phi in enumerate(phis,1):
    ck('COMMON_algebraic_adjoint_'+str(j),Lstar(phi))
    ck('COMMON_Euler_adjoint_'+str(j),E0(E0(phi))+6*E0(phi)+S.Rational(80,9)*phi)

P1=t*U*z/(2*R*R)+3*U*(U+W)/(16*R*R)
P2=3*(U+W)/(8*z)
forms=[
 (3*C/(2*R*R*z),(W*W*DU(C)-S.Rational(5,2)*U*C)/(R**3*z),P1,-3*kap/16,-kap/16),
 (3*C/(2*z*z*W),(W*DU(C)-S.Rational(3,2)*U*C/W)/(R*z*z),P2,t/2,-t/2)
]
records=[]
for j,(aa,bb,pp,ls,lr) in enumerate(forms,1):
    ck('FULL_Green_closed_fixed_t_'+str(j),DU(bb)-DR(aa))
    ck('FINITE_actual_potential_U_'+str(j),aa-DU(pp)-ls*DU(SS)/SS)
    ck('FINITE_actual_potential_R_'+str(j),bb-DR(pp)-ls*DR(SS)/SS-lr/R)
    TT=S.factor(-DT(pp)-ls*DT(SS)/SS)
    ck('FULL_t_normal_coefficient_'+str(j),DT(pp)+ls*DT(SS)/SS+TT)
    if j==1:
        simpleT=-U*z*(t**3-1)/(2*R*R*rho*rho)-9*kap/(32*t*rho*rho)
        n=S.cancel(TT-simpleT).as_numer_denom()[0]
        n=S.rem(n,W*W-U*U+kap*R*R,W)
        checks['FIRST_Green_dt_unit_simplifies_physically']=S.factor(S.rem(n,rho*rho-2*t**3+1,rho))==0
        assert checks['FIRST_Green_dt_unit_simplifies_physically']
        TT=simpleT
    records.append({'P':str(pp),'dlogS_coefficient':str(ls),'dlogR_coefficient':str(lr),'full_dt_correction':str(TT)})

# Prescribed derivative-C1 Green pair: this removes the low Euler component.
C1=DU(C)
L1=lambda f:W*W*DU(DU(f))+S.Rational(3,2)*U*DU(f)-S.Rational(3,2)*R*DR(f)+f/2
L1star=lambda f:W*W*DU(DU(f))+S.Rational(5,2)*U*DU(f)+S.Rational(3,2)*R*DR(f)+S.Rational(5,2)*f
ck('DERIVATIVE_C1_pure_Euler_weight',E0(C1)-C1/3)
ck('DERIVATIVE_C1_physical_heat',L1(C1))
P_high=3*U*(U+W)/(16*R*R)
C1_records=[]
C1_forms=[]
for label,phi,sgn in [('U',U/(R**3*z),1),('W',W/(R**3*z),-1)]:
    ck('DERIVATIVE_C1_common_adjoint_'+label,L1star(phi))
    ck('DERIVATIVE_C1_adjoint_Euler_'+label,E0(phi)+S.Rational(7,3)*phi)
    FU=W*W*(phi*DU(C1)-C1*DU(phi))-U*phi*C1/2
    FR=-3*R*phi*C1/2
    aa=-FR;bb=FU
    ls=sgn*3*kap/16;lr=sgn*kap/16
    ck('DERIVATIVE_C1_closed_'+label,DU(bb)-DR(aa))
    ck('DERIVATIVE_C1_finite_U_'+label,aa-DU(P_high)-ls*DU(SS)/SS)
    ck('DERIVATIVE_C1_finite_R_'+label,bb-DR(P_high)-ls*DR(SS)/SS-lr/R)
    TT=(-9*kap*(2*U-W)/(32*t*rho*rho*W) if sgn==1
        else -9*kap/(32*t*rho*rho))
    ck('DERIVATIVE_C1_full_t_normal_'+label,DT(P_high)+ls*DT(SS)/SS+TT)
    C1_forms.append((aa,bb))
    C1_records.append({'label':label,'phi':str(phi),'omega_U':str(aa),'omega_R':str(bb),
                       'P_high':str(P_high),'dlogS_coefficient':str(ls),'dlogR_coefficient':str(lr),
                       'full_dt_correction':str(TT)})
ck('DERIVATIVE_C1_sum_is_two_dP_U',C1_forms[0][0]+C1_forms[1][0]-2*DU(P_high))
ck('DERIVATIVE_C1_sum_is_two_dP_R',C1_forms[0][1]+C1_forms[1][1]-2*DR(P_high))

d=t/(4*rho);r=R-d;K=r*r-U*U
psiU=2*r/K;psiR=-2*U/K
gamU=DU(SS)/SS;gamR=DR(SS)/SS-1/R
ck('SOURCE_gamma_U',gamU-1/W)
ck('SOURCE_gamma_R',gamR+U/(R*W))
ck('SOURCE_actual_Psi_Green_pair',psiU*gamR-psiR*gamU-2*d*U/(K*R*W))
ck('SOURCE_actual_Psi_dlogR_pair',psiU/R-2*r/(K*R))

out={
 'status':'PASS_TWO_EXPLICIT_FINITE_PHYSICAL_GREEN_CONCOMITANTS_AND_SOURCE_PAIRINGS; NOT_TWO_ROW_CLOSURE',
 'physical_field':'rho^2=2t^3-1,kappa=4t^3/rho^2,z^3=R/rho,W^2=U^2-kappa R^2,r=R-t/(4rho),C=tz^2/3+z(U+W)/4. Every derivative in U,R is on this field at fixed t.',
 'PDEs':'[(E0-2/3)(E0-4/3)]C=0; [W^2 DU^2-(U/2)DU-(3R/2)DR+1]C=0,E0=U DU+R DR.',
 'common_adjoints':'phi1=1/(R^3 z),phi2=1/(R z^2 W). Both solve Lstar phi=0 and (E0+8/3)(E0+10/3)phi=0. Lstar=W^2 DU^2+(9U/2)DU+(3R/2)DR+5.',
 'omega1':'3C dU/(2R^2z)+(W^2 CU-5UC/2)dR/(R^3z)',
 'omega2':'3C dU/(2z^2W)+(W CU-3UC/(2W))dR/(Rz^2)',
 'FULL_finite_potentials':'omega_i=dP_i+ls_i*dlog(U+W)+lr_i*dlogR+T_i*dt, with all coefficients and the rational T_i listed below. No logarithm is used as a rational scalar potential.',
 'records':records,
 'DERIVATIVE_C1_pure_weight':'C1=DU(C) has E0 C1=C1/3 and [W^2 DU^2+(3U/2)DU-(3R/2)DR+1/2]C1=0. The common algebraic adjoints are phi_U=U/(R^3 z),phi_W=W/(R^3 z), each E0-weight -7/3.',
 'DERIVATIVE_C1_records':C1_records,
 'DERIVATIVE_C1_full_potentials':'For each label, omega=omega_U*dU+omega_R*dR=dP_high+ls*dlog(U+W)+lr*dlogR+T*dt. Their sum is 2dP_high modulo dt; their difference is (3kappa/8)dlog(U+W)+(kappa/8)dlogR modulo dt. All full t corrections are listed.',
 'full_t_derivation':'At fixed U,R: rho_t=3t^2/rho,z_t=-t^2z/rho^2,kappa_t=-3kappa/(t rho^2),W_t=3kappa R^2/(2t rho^2W). Thus the displayed T_i retain the complete physical t-normal. eta=dt/rho kills exactly T_i dt.',
 'source_pair':'psi=dlogPsi=2(r dU-U dR)/K,K=r^2-U^2; gamma=dlog[(U+W)/R]=(dU-U dR/R)/W. EXACT: psi wedge gamma=2d*U*dU wedge dR/(K R W),psi wedge dlogR=2r*dU wedge dR/(K R).',
 'finite_source_currents':'eta wedge psi wedge omega2=d[eta wedge psi*P2]+(t/2)eta wedge psi wedge gamma. eta wedge psi wedge omega1=d[eta wedge psi*P1]-(3kappa/16)eta wedge psi wedge gamma-(kappa/4)eta wedge psi wedge dlogR. These retain actual Psi, both W branches and all original C terms.',
 'remaining':'To serve the prescribed two-row target, the actual rational residual must equal a weighted combination of these full Green packets with all derivatives of the weights retained. No such source equality or rational A serving both rows is asserted.',
 'checks':checks,'check_count':len(checks)
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'finite actual Green concomitant, full-normal and source-pair identities')
