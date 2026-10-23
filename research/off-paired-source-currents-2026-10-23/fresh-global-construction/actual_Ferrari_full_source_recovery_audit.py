"""Independent literal Ferrari correspondence and whole-source recovery.

The pair source is not shown exact here. This audits the actual finite cover,
covariant normal, residue, and recovery factor required by a future primitive.
"""
from pathlib import Path
import itertools,json,time
import sympy as S
start=time.monotonic()
g,c,H,L,D,xi,eps,ze,w,ell,v,E,F=S.symbols('g c H L D xi eps zeta w ell v E F',nonzero=True)
x,b,z,e,f=S.symbols('x b z e f')
P=g**4+L*g**3+H*g*g+D*g+1
Pg=S.diff(P,g);Pgg=S.diff(Pg,g)
R=(ze-H)*(ze*ze-4)-L*L-D*D+L*D*ze
Rz=S.diff(R,ze);Rzz=S.diff(Rz,ze)
zc=c+1/c
al=(L*c*c-D*c)/(c*c-1);be=(D*c-L)/(c*c-1)
q=g*g+al*g+c;qb=g*g+be*g+1/c
checks={}
def ck(n,z):
    checks[n]=S.cancel(z)==0
    assert checks[n],n

# Independently bind the original projective orientation and whole normal.
Fo=x**6+b**6+1+z**6+e**6+f**6+x**3*b*z/2+b**3*z*e*f/2+x*x*b*e*f/3
trans=[ell*xi,ell**2,ell*v,ell*E,ell*F]
Jac=S.det(S.Matrix([[S.diff(a,u)for u in(ell,v,xi,E,F)]for a in trans]))
Hp=xi**6+v**6+E**6+F**6+v*xi**3/2+xi*xi*E*F/3
Lp=v*E*F/2
ck('original_whole_polynomial',Fo.subs(dict(zip((x,b,z,e,f),trans)),simultaneous=True)-P.subs({g:ell**3,H:Hp,L:Lp,D:0}))
ck('original_chart_orientation_Jacobian',Jac-2*ell**5)
ck('whole_source_after_g_change',ell**3*xi**3*Jac/(3*ell**2)-S.Rational(2,3)*xi**3*ell**6)
ck('actual_epsilon_family',
 (Fo-eps*x**3).subs(dict(zip((x,b,z,e,f),trans)),simultaneous=True)
 -P.subs({g:ell**3,H:Hp,L:Lp,D:-eps*xi**3}))

# Actual cover diagram: T->original has degree2, T->quartic has degree3.
# The original mu3 source symmetry makes these maps compatible, but no
# Fano or quotient-coniveau conclusion is used.
ck('double_cover_involution_P',P.subs({g:-g,L:-L,D:-D},simultaneous=True)-P)
ck('double_cover_involution_physical_D',(-eps*xi**3).subs(xi,-xi)+(-eps*xi**3))
mu3_weights=(1,2,1,1,1) # x,b,z,e,f; source x³ dxdbdzde df
checks['original_mu3_whole_source_invariant']=(3*mu3_weights[0]+sum(mu3_weights))%3==0

# Ferrari incidence and both moving coefficient normals are checked on the
# actual selected quadratic, not by freezing its constant term.
Hinc=zc+al*be
ck('exact_incidence_factor',q*qb-P-g*g*R.subs(ze,zc)/(zc*zc-4))
zD=(2*D-L*ze)/Rz
cD=c*c*zD.subs(ze,zc)/(c*c-1)
alD=S.diff(al,D)+S.diff(al,c)*cD
beD=S.diff(be,D)+S.diff(be,c)*cD
gDq=-(alD*g+cD)/(2*g+al)
inc_normal=S.together(gDq+g/Pg)
num,den=inc_normal.as_numer_denom()
num=S.together(num.subs(H,Hinc)).as_numer_denom()[0]
checks['FULL_covariant_selected_root_normal']=S.cancel(S.rem(num,q,g))==0
assert checks['FULL_covariant_selected_root_normal']
ck('FULL_covariant_L_coefficient',alD+beD)
ck('FULL_covariant_D_coefficient',alD/c-al*cD/c**2+beD*c+be*cD-1)
ck('FULL_covariant_H_coefficient',(cD*(1-1/c**2)+alD*be+al*beD).subs(H,Hinc))
ck('physical_resolvent_epsilon_normal',(-xi**3*zD).subs(D,0)-xi**3*L*ze/Rz.subs(D,0))

# Marked-root double-pole residue and the explicit ambient pole reduction.
Nroot=S.Rational(2,3)*xi**3*g*g
beta_root=(S.diff(Nroot,g)*Pg-Nroot*Pgg)/Pg**3
volroot=S.Rational(2,3)*g/Pg
covD=lambda f:S.diff(f,D)-g/Pg*S.diff(f,g)
ck('literal_marked_source_as_full_normal',beta_root+xi**3*covD(volroot))
nu=Nroot/Pg
ck('quartic_ambient_normal_reduction_density',S.diff(nu,g)/Pg-beta_root)

# Trace of g/Pg over the chosen quadratic, by an independent remainder
# calculation. R=0 is imposed only after retaining the off-incidence defect.
bb,aa=S.symbols('bb aa')
u=bb-aa;k=1/c-c
norm=k*k-aa*u*k+c*u*u
inverse=(k-aa*u-u*g)/norm
rr=S.rem(S.together((g*inverse-(k*g+c*u)/norm)*norm),g*g+aa*g+c,g)
ck('independent_quadratic_trace_remainder',rr)
Rzc=Rz.subs(ze,zc)
ck('independent_resultant_incidence_unit',(norm.subs({aa:al,bb:be})-Rzc+2*zc*R.subs(ze,zc)/(zc*zc-4)))
pairvol=-S.Rational(2,3)*w/Rz

# Compute the pair double-pole residue directly on w²=zeta²-4. This
# independently checks the claimed ambient source, including w_zeta.
Npair=-S.Rational(2,3)*xi**3*L*ze*w
Npair_z=S.diff(Npair,ze)+S.diff(Npair,w)*ze/w
pair_raw=(Npair_z*Rz-Npair*Rzz)/Rz**3
wD=ze*zD/w
pair_normal=-xi**3*(S.diff(pairvol,D)+S.diff(pairvol,ze)*zD+S.diff(pairvol,w)*wD)
# Off D=0, epsilon differentiation has the actual coefficient L*zeta-2D.
Npair_general=S.Rational(2,3)*xi**3*w*(2*D-L*ze)
Nz=S.diff(Npair_general,ze)+S.diff(Npair_general,w)*ze/w
pair_general=(Nz*Rz-Npair_general*Rzz)/Rz**3
ck('FULL_general_pair_residue_covariant_normal',pair_general-pair_normal)
R0=R.subs(D,0);Rz0=Rz.subs(D,0)
compact=4*xi**3*L*(H*ze**3-2*ze**2-8)/(3*w*Rz0**3)
num=S.together(pair_raw.subs(D,0)-compact).as_numer_denom()[0]
num=S.rem(S.rem(num,w*w-ze*ze+4,w),R0,ze)
checks['physical_pair_source_ALL_conic_and_cubic_normals']=S.factor(num)==0
assert checks['physical_pair_source_ALL_conic_and_cubic_normals']
ck('actual_R_epsilon_quadratic_term',R.subs(D,-eps*xi**3)-(R0-eps*xi**3*L*ze-eps**2*xi**6))

# The incidence matrix is constant on the full labelled splitting cover.
# Thus its recovery identity commutes with every coefficient derivative and
# exterior differential; no unweighted all-root trace is a primitive.
pairs=list(itertools.combinations(range(4),2))
T=S.Matrix([[int(i in pair)for i in range(4)]for pair in pairs])
checks['literal_incidence_recovery_matrix']=T.T*T==2*S.eye(4)+S.ones(4)
# A rational coefficient may multiply the physical normal. Its action on
# DIFFERENTIALS is the Lie derivative; the omitted dxi term is recorded.
checks['covariant_normal_dD_leg_retained']=S.diff(-xi**3,xi)==-3*xi*xi

# A concrete actual physical base, six pairs, and four recovered original
# complex points. This is independent of symbolic placeholder cancellation.
point={H:S.Rational(29,6),L:S.Rational(1,2),D:0,xi:1}
Ppoint=P.subs(point)
checks['concrete_physical_quartic_separable']=S.discriminant(Ppoint,g)!=0
roots=S.nroots(Ppoint,n=65,maxsteps=200)
vals=[S.N(beta_root.subs(point).subs(g,r),55)for r in roots]
vvals=[S.N(volroot.subs(point).subs(g,r),55)for r in roots]
tol=S.Float('1e-45');pairvals={};maxerr=S.Float(0)
for ij in pairs:
 i,j=ij;cc=roots[i]*roots[j];zz=cc+1/cc;ww=cc-1/cc
 pv=S.N(compact.subs(point).subs({ze:zz,w:ww}),55)
 hv=S.N((-S.Rational(2,3)*w/Rz).subs(point).subs({ze:zz,w:ww}),55)
 err=max(abs(S.N(pv-vals[i]-vals[j],50)),abs(S.N(hv-vvals[i]-vvals[j],50)))
 maxerr=max(maxerr,err);pairvals[ij]=pv
checks['concrete_SIX_pair_whole_sources_and_volumes']=maxerr<tol
checks['concrete_ALL_root_source_trace_zero']=abs(S.N(sum(vals),50))<tol
recovererr=max(abs(S.N(sum(vv for ij,vv in pairvals.items()if i in ij)/2-vals[i],50))for i in range(4))
checks['concrete_FOUR_marked_sources_recovered']=recovererr<tol
originalerr=S.Float(0)
for r in roots:
 el=S.N(r**S.Rational(1,3),60)
 coords={x:el,b:el*el,z:el,e:el,f:el}
 originalerr=max(originalerr,abs(S.N(Fo.subs(coords),50)))
checks['concrete_FOUR_original_sextic_points']=originalerr<tol
assert all(checks.values()),{k:v for k,v in checks.items()if not v}

out={
 'status':'INDEPENDENT_FULL_SOURCE_FERRARI_FINITE_RECOVERY_PASS; PAIR_PRIMITIVE_OPEN',
 'check_count':len(checks),'checks':{k:bool(v)for k,v in checks.items()},
 'original_binding':'Y0=1,(x,b,z,e,f)=(X0,X1,Y1,X2,Y2), Omega5=+dx db dz de df. The projective sign and z/e permutation cancel. x=ell*xi,b=ell²,z=ell*v,e=ell*E,f=ell*F,g=ell³.',
 'whole_source':'(2/3)xi³g² dg dv dxi dE dF/P². P=g4+Lg3+Hg2+Dg+1, physical D=−epsilon*xi³. H,L are the actual four-variable polynomials, not independent target replacements.',
 'finite_cover_diagram':'T=(ell,v,xi,E,F),ell³=g. T->original X has degree2 (ell->−ell, four base variables->their negatives); T->quartic W has degree3 (ell->zeta3 ell with g and bases fixed). The latter maps to a surviving original mu3 symmetry. The source descends literally to W. No quotient/Fano inference is used.',
 'complete_normal':'zeta_D=(2D−Lzeta)/Rz,c_D=c²zeta_D/(c²−1); alpha_D,beta_D are total through c_D. The selected-root derivative from q is EXACTLY g_D=−g/Pg. This also holds for the physical epsilon normal after multiplication by−xi³.',
 'pair_source_ambient':'−2xi³Lzeta*w dzetadvdxidEdF/(3R²), at D=0, with w²=zeta²−4. Its direct double-pole residue equals the full normal derivative of−2w/(3Rz). All conic/cubic-normal and nonconstant xi factors are retained.',
 'pair_source_density':'4xi³L(H zeta³−2zeta²−8)/(3w Rz³) dbase4',
 'ambient_correction':'For Nroot=(2/3)xi³g² and nu=Nroot/Pg, Nroot*Omega/P²=nu_g*Omega/P−d[nu*i_(partial_g)(Omega)/P]. Res(nu_g*Omega/P) is the audited beta_root. The pair cubic has the identical formula with its actual conic derivative d/dzeta(w)=zeta/w.',
 'FULL_finite_recovery':'Tpair^* Tpair=2Id+allones. Sum_i g_i/Pg_i=0 by Lagrange residue; its full physical normal derivative also sums to0. Therefore beta_i=(1/2)sum_{j!=i}beta_{ij}, literally with the full moving-sheet normals. Traces commute with d and the full Lie normal, not coefficient-only partial derivatives.',
 'primitive_recovery_factor':'If a rational3-current Jpair serves the displayed WHOLE pair4-source on R=0,w²=zeta²−4, use JW=(1/2)Tr_{I/W}(pullback Jpair). Pull JW to T and use JX=(1/2)Tr_{T/X}(pullback JW). Thus the unnormalized combined trace factor is1/4. There is no extra factor1/3: T->W is pulled back, not traced.',
 'normal_form_caution':'Because delta_epsilon D=−xi³, its Lie action sends dD to−3xi² dxi. Top-base4 density calculations kill that extra wedge legitimately. A future current with fewer base legs must transport that normal leg explicitly, or pull the full family back by D=−epsilon xi³ before differentiating.',
 'concrete_physical_test':{'v':1,'xi':1,'E':1,'F':1,'H':'29/6','L':'1/2','D':0,'all_six_pair_error':str(maxerr),'four_source_recovery_error':str(recovererr),'four_original_point_error':str(originalerr)},
 'scope':'Positive actual finite source-recovery audit only. No primitive for the complement-odd pair source has been constructed; no certificate or legal denominator follows from factorization or total tracezero. Frozen publication is unchanged.',
 'elapsed_seconds':round(time.monotonic()-start,3),
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'independent whole-source Ferrari finite recovery and normals; pair primitive remains open',flush=True)
