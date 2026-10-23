"""Independent WHOLE physical audit of the actual two-cotangent source current.

The pullback contains no r,S,mark-Y roots.  The full four-coordinate
derivative is computed directly; neither endpoint compact rows nor fiber
cochains are projected away.  The two coefficient defects remain explicit.
"""
from pathlib import Path
import json,time
st=time.time()
pth=(Path(__file__).parents[1]/'full-rank4-source-assembly/actual_two_cotangent_source_Cartan_current.py')
ns={'__file__':str(pth)}
exec(compile(pth.read_text().split('checks={')[0],str(pth),'exec'),ns)
W,E2=ns['W'],ns['E2']
R,D,a,V,A,kS,L,K,B=[ns[x] for x in ('R','D','a','V','A','kS','L','K','B')]
u,v,cl,cn,q,ln,p,R1,I1=[ns[x] for x in ('u','v','cl','cn','q','ln','p','R1','I1')]
native=ns['native'];m=native['ns']['m'];vR,va=E2(ns['vR']),E2(ns['va'])
# The source density continuity uses div_CMmass, while this current has
# canonical volume dy*dell*dmu. Its Jacobian K is a moving unit.
gamma_unit=(vR*B(K)+va*K.diff(2))/K
gamma_mass=B(vR)+va.diff(2)-vR*(kS+1/(2*R))
def independent_Nbase(z):
    z=W(z)
    return W(vR*z.Bcoef()+va*z.z.diff(2),z.ar,z.bs)
cl=independent_Nbase(u)+W(gamma_mass+gamma_unit)*u
cn=independent_Nbase(v)+W(gamma_mass+gamma_unit)*v
z=E2(m)+E2(a/(6*A));P=E2(A*m**3+a*m*m/2+(D+a/3)*m)-V*a**3
Pm=P.diff(3);f=P*P-4*R
X=W(z,-1,1);Bx=X*X/2+W(L/3,0,-1)
F=(u*X+v*Bx)/W(E2(1),0,1)
Fdef=(cl*X+cn*Bx)/W(E2(1),0,1)
assert (F.ar,F.bs)==(0,0) and (Fdef.ar,Fdef.bs)==(0,0)
bb=E2(a/(6*A))
Nm=vR*(1/(2*R)-kS)*z-vR*B(bb)-va*bb.diff(2)+1/(3*A)
N=[vR,vR*D/R,va,Nm]
C=E2(18*R/D)*K*F.z
w=[C*Pm*N[i] for i in range(3)]+[C*(Pm*Nm-m*m)]
print('Independent physical vector built',round(time.time()-st,3),flush=True)
checks={}
def ck(name,z):
    checks[name]=not bool(z)
    assert checks[name],name
ck('whole_forward_normal_source_NP',sum((N[i]*P.diff(i) for i in range(4)),E2(0))-P*vR/(2*R)-m*m)
ck('canonical_divergence_has_moving_K_unit',sum((N[i].diff(i) for i in range(4)),E2(0))-2*vR/R-gamma_mass)
ck('whole_physical_vector_log_tangent',sum((w[i]*P.diff(i) for i in range(4)),E2(0))-P*w[0]/(2*R))
g0=3*(q*R1+p*I1);g1=-3*R1
grow=g0+g1*X
assert (grow.ar,grow.bs)==(0,0)
target=E2(18*R/D)*K*grow.z
remainder=-E2(18*R/D)*K*Pm*Fdef.z
# If J=-i_w(vol/(72 R sqrtD h)), w(P)=P*wR/(2R), its literal
# derivative is (-div(w)+3wR/(2R)+wD/(2D))*vol/(72R sqrtD h).
literal=-sum((w[i].diff(i) for i in range(4)),E2(0))+3*w[0]/(2*R)+w[1]/(2*D)
print('Independent WHOLE four-coordinate derivative built',round(time.time()-st,3),flush=True)
ck('WHOLE_literal_physical_source_and_both_cotangent_defects',literal-target-remainder)
# Also bind the exact physical coefficient normalization of the canonical
# relative lambda/nu defects. This does not identify either with zero.
assert (cl.ar,cl.bs)==(1,0) and (cn.ar,cn.bs)==(0,2)
Fdef_explicit=cl.z*z+cn.z*A*(z*z/2+L/(3*A))
ck('both_secondkind_defect_source_units',Fdef.z-Fdef_explicit)
out={
 'status':'PASS_WHOLE_ORIGINAL_PHYSICAL_TWO_COTANGENT_SOURCE_CURRENT; TWO_COEFFICIENT_DEFECTS_RETAINED',
 'checks':checks,'check_count':len(checks),
 'physical_frame':'P=A*m³+a*m²/2+(D+a/3)m−Va³,h²=P²−4R,A=(R³+1)/R,V²=4R+R²/(4D). vol=dR*dD*da*dm. Every constrained V derivative is retained.',
 'actual_current':'Let z=m+a/(6A),F=(uX+v(X²/2+ell/3))/S. Then J_N=−i_w[vol/(72R sqrtD h)],w=(18RKF/D)*(P_m*Nphys−m²*e_m). F is rational in R,D,a,m,V; all r,S and moving-mark roots cancel.',
 'Nphys':'(vR,D*vR/R,va,(1/(2R)−kS)*vR*z−vR*B[a/(6A)]−va/(6A)+1/(3A)). Its literal NP=P*vR/(2R)+m² is checked globally.',
 'whole_source':'Omega*(g0*omega0+g1*omega1)=dJ_N−Omega*(C_lambda*lambda+C_nu*nu),Omega=dy*dell*dmu,g0=3(qR1+pI1),g1=−3R1. This agrees with the independently fixed source alpha-lambda row.',
 'physical_identity':'dJ_N=[18RK/D]*(g0+g1X−P_m*Fdef)*vol/(72R sqrtD h),Fdef=(C_lambda*X+C_nu*(X²/2+ell/3))/S. The entire literal four-coordinate derivative equals this rational expression globally.',
 'both_channels':'C_lambda=r*c_lambda,C_nu=S²*c_nu. Fdef=c_lambda*z+A*c_nu*(z²/2+L/(3A)). Both defects are retained; no rank1 simplification or compact-row deletion is used.',
 'canonical_unit_correction':'The sourceagent export initially used gamma_CM=B(vR)+va_a−(kS+1/(2R))*vR. The literal current with canonical volume requires gamma_can=gamma_CM+Nbase(K)/K. The entire derivative is independently checked with this moving Jacobian unit restored. rho=−f0*gamma_CM is still the correct density continuity identity.',
 'formula_artifact':'Actual u,v and gamma_CM data in full-rank4-source-assembly/actual_two_cotangent_source_Cartan_current.py/json. Use C_lambda=(Nbase+gamma_can)u and C_nu=(Nbase+gamma_can)v; the rational formulas above fully specify this physical current without large expanded coefficient exports.',
 'remaining_zero':not bool(remainder),
 'scope':'One explicit source-bound rational current and full physical identity, independently audited. It is NOT a certificate: both displayed coefficient defects still require a source-serving current with all weight, section and finite-trace costs.',
 'elapsed_seconds':round(time.time()-st,3),
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'WHOLE actual two-cotangent physical source audit',round(time.time()-st,3),flush=True)
