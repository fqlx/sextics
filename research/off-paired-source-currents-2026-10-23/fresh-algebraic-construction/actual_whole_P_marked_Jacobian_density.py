"""Actual full-P second mark, Jacobian density, and physical-normal charge.

The inverse-branch density K is retained.  No rational Toda descent or scalar
primitive is asserted by this file.
"""
import json
from pathlib import Path
import sympy as s

R,D,V,a,m,z,delta,U,y=s.symbols('R D V a m z delta U y',nonzero=True)
A=R**2+1/R
Slog=R**2/(R**3+1)
L=D+a/3-a*a/(12*A)
M=-a*L/(6*A)-(V+1/(216*A*A))*a**3
P=A*m**3+(a/2)*m*m+(D+a/3)*m-V*a**3
dL=-a/(3*A)
dM=-D/(3*A)-a/(9*A)+a*a/(18*A*A)
B=lambda f:s.diff(f,R)+D/R*s.diff(f,D)+V/(2*R)*s.diff(f,V)
La=s.diff(L,a);Ma=s.diff(M,a)
LR=B(L)-Slog*L;MR=B(M)-M/(2*R)
K=s.factor(Ma*LR-La*MR)
vR=s.factor((dL*Ma-La*dM)/K)
va=s.factor((LR*dM-MR*dL)/K)
Kd=s.diff(dM,a)*LR+Ma*(B(dL)-Slog*dL)-s.diff(dL,a)*MR-La*(B(dM)-dM/(2*R))
checks={}
def ck(name,expr):
    ok=s.factor(expr)==0
    checks[name]=ok
    assert ok,(name,s.factor(expr))

ck('actual_P_to_depressed_genus_two',
   P.subs(m,z-a/(6*A))-(A*z**3+L*z+M))
Ld=D+a/3-(a/2+delta)**2/(3*A)
Md=2*(a/2+delta)**3/(27*A*A)-(a/2+delta)*(D+a/3)/(3*A)-V*a**3
ck('whole_depressed_delta_family',
   (P+delta*m*m).subs(m,z-(a/2+delta)/(3*A))-(A*z**3+Ld*z+Md))
ck('actual_depressed_L_normal',s.diff(Ld,delta).subs(delta,0)-dL)
ck('actual_depressed_M_normal',s.diff(Md,delta).subs(delta,0)-dM)
ck('whole_depression_Cartan_numerator',
   (dL*z+dM+(3*A*z*z+L)/(3*A))-(z-a/(6*A))**2)
ck('marked_y_fixed_R_derivative_D',B(D)-D/R)
ck('marked_y_fixed_R_derivative_V',B(V)-V/(2*R))
ck('actual_missing_normal_baseflow_L',LR*vR+La*va-dL)
ck('actual_missing_normal_baseflow_M',MR*vR+Ma*va-dM)
ck('source_forced_baseflow_R_numerator',
   dL*Ma-La*dM-R*(3*D+a+27*V*a**3)/(27*(R**3+1)))
ck('global_K_at_even_member',K.subs(a,0)+D*D/(6*(R**3+1)**2))
ck('source_forced_baseflow_at_even_member_a',va.subs(a,0)-2)
ck('source_forced_baseflow_at_even_member_R',
   vR.subs(a,0)+2*R*(R**3+1)/(3*D))
Del0=s.factor((Kd-vR*B(K)-va*s.diff(K,a)).subs(a,0))
ck('whole_density_normal_at_even_member',
   Del0-D*(3*R**3-1)/(9*(R**3+1)**2))

# This source coefficient, although written with sqrtR on the physical
# cover, is an actual rational function of the canonical second mark.
N=2*V*D/R**s.Rational(3,2)
ck('physical_normal_charge_is_leaf_constant',B(N))
ck('physical_normal_charge_is_a_constant',s.diff(N,a))
# y=sqrtR/U and v0=V/sqrtR.  N=v0/(2y^2).
ck('physical_normal_charge_descends_to_mark',
   (N-(V/s.sqrt(R))/(2*y*y)).subs(D,R/(4*y*y)))

# Direct generic determinant identity, then actual physical B derivatives.
# Keeping the first derivatives as independent symbols avoids a huge,
# unnecessary multivariate rational gcd inside SymPy's determinant method.
SR,rr=s.symbols('Sroot rroot',nonzero=True)
lR,lU,lA,mR,mU,mA,lv,mv=s.symbols('lR lU lA mR mU mA lv mv')
mat=s.Matrix([
 [(lR-Slog*lv)/SR,lU/SR,lA/SR],
 [(mR-mv/(2*R))/rr,mU/rr,mA/rr],
 [rr/(2*R*U),-rr/U**2,0]
])
jj=(mat[0,0]*mat[1,2]/U+mat[0,1]*mat[1,2]/(2*R)
    +mat[0,2]*(-(mR-mv/(2*R))/(rr*U)-mU/(2*R*rr)))*rr/U
genericK=mA*(lR+U*lU/(2*R)-Slog*lv)-lA*(mR+U*mU/(2*R)-mv/(2*R))
ck('WHOLE_marked_base_Jacobian_K_over_SU2',jj-genericK/(SR*U**2))
V_R=(2+R/U**2)/V;V_U=-R**2/(U**3*V)
ck('actual_B_on_V_from_both_physical_normals',
   s.expand(((V_R+U*V_U/(2*R))-V/(2*R))*V).subs(V**2,4*R+R**2/U**2))

out={
 'status':'ACTUAL_FULL_P_MARKED_JACOBIAN_DENSITY_AND_PHYSICAL_CHARGE; SOURCE_PRIMITIVE_OPEN',
 'checks':checks,'check_count':len(checks),
 'actual_full_P':'P=A*m^3+(a/2)*m^2+(D+a/3)*m-V*a^3, A=(R^3+1)/R,D=U^2/4,V^2=4R+R^2/U^2; h^2=P^2-4R. The actual missing normal is P_delta=m^2.',
 'actual_second_mark':'Choose t with P(t,a)=V. Then Q=(t,R/U) is a literal point on the SAME full genus2 curve. Choose r^2=R,S^3=R^3+1,c=S/r. With ell=L/S,mu=M/r,X=c*(m+a/(6A)),Y=h/r, the canonical curve is Y^2=(X^3+ell*X+mu)^2-4. Q has XQ=c*(t+a/(6A)),YQ=r/U. This is a finite mark construction, not a claim the leaf is rational.',
 'actual_base_dominance':'Let y=YQ=r/U. The determinant J_y=d(ell,mu,y)/d(R,U,a) is K/(S*U^2). At a=0, K=-D^2/[6(R^3+1)^2], hence is nonzero generically. Off the finite mark branch 3XQ^2+ell=0, this proves full marked-base dominance.',
 'L':str(L),'M':str(s.factor(M)),
 'B':'B=d_R+(U/(2R))*d_U; equivalently B(D)=D/R and B(V)=V/(2R). It holds the ACTUAL mark y=sqrtR/U fixed.',
 'K_definition':'K=M_a*(B(L)-R^2*L/(R^3+1))-L_a*(B(M)-M/(2R))',
 'K':str(K),
 'WHOLE_first_pole_density':'With orientation dR dU da dX_P, the first-pole form after the literal 2-isogeny and full-P chart is r/(36*V*U^2*S) dR dU da dX_P/Y_P. Therefore on the actual two-point cover it is [FQ/(36K)] d_ell d_mu dXQ/YQ dXP/YP, FQ=3XQ^2+ell. The inverse-branch unit 1/K is compulsory.',
 'whole_depression_cochain':'For P_delta=A*m^3+(a/2+delta)*m^2+(D+a/3)*m-V*a^3, let m=z-(a/2+delta)/(3A). Exactly partial_delta(dm wedge da/h)=pullback(partial_delta(dz wedge da/h))+d[da/(3A*h)]. Thus with the actual source factor1/(72R), its rational source cochain is +dU wedge dR wedge da/(216R*A*h). All R/U base derivatives wedge out only against the full base form.',
 'actual_normal_partials':{'L_delta':str(dL),'M_delta':str(dM)},
 'source_forced_baseflow':{'R_component':str(vR),'a_component':str(va),'U_component':'U*vR/(2R)'},
 'physical_normal_charge':'N=VU^2/(2R^(3/2))=(V/r)/(2y^2)=(zQ+zQ^-1)/(2(zQ-zQ^-1)^2). It descends RATIONALLY to the actual canonical second mark and is constant under B and d_a. Thus no N derivatives are omitted when the marked-base Jacobian is differentiated.',
 'WHOLE_fixed_target_density_normal':'For delta the missing-m^2 normal, form K_delta by differentiating its displayed L,M formula (A,R,U,V fixed). Let Vbase=vR*B+va*d_a. At fixed canonical (ell,mu,Q), the density normal is rho_delta=FQ*(Vbase(K)-K_delta)/(36K^2). The physical epsilon normal is N*rho_delta because B(N)=d_a(N)=0. The moving-map Cartan current must be added; this formula does not drop it or imply source descent.',
 'density_normal_even_member':'At a=0, K_delta-Vbase(K)=D*(3R^3-1)/[9(R^3+1)^2], so rho_delta/FQ=-(3R^3-1)*(R^3+1)^2/(9D^3). This exact retained source is nonzero and does not settle the whole current.',
 'open':'Integrate this actual finite-branch density or construct the full source-serving correspondence/cochain. Rationality of universal Toda separation coordinates alone does not remove K, and no certificate is asserted.'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual full-P marked Jacobian, complete density and physical normal charge; primitive open')
