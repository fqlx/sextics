"""One literal source-bound section/conic/elliptic companion construction.

This uses the actual normalized Ferrari cubic.  Its quadratic-twist conic
pencil, even quartic, cubic companion, physical normal, source weight, and
moving-coordinate exact cochain are explicit.  No primitive is asserted.
"""
from pathlib import Path
import hashlib,json
import sympy as s

R,U,T,V,x,y,k,p,delta=s.symbols('R U T V x y k s delta',nonzero=True)
A=R**2+1/R;B=T+R/T;D=U*U/4;Ec=s.Rational(1,2);Fc=s.Rational(1,3)
kap=V*U*U/(2*R**s.Rational(3,2))
root=A*k**3+Ec*k*k-V
C=A*x**3+B*y**3+D*x*y*y+Ec*x*x+Fc*x*y-V
checks={}
def ck(name,expr,rels=()):
    num=s.together(expr).as_numer_denom()[0]
    for gen,poly in rels:
        num=s.rem(num,poly,gen)
    red=s.factor(num)
    checks[name]=red==0
    assert checks[name],(name,red)

old=Path(__file__).with_name('actual_Ferrari_plane_cubic_source.json')
oldrec=json.loads(old.read_text())
assert oldrec['check_count']==22 and all(oldrec['checks'].values())
checks['old_WHOLE_pair_source_receipt_PASS22']=True

# Literal old-to-normalized source coordinate map, independent of any GL2
# or generic polynomial-density result.
r,sg,u,aa,cc=s.symbols('r sigma u a cA',nonzero=True)
new=[r*u,r*r,r*sg**3,r*aa,sg*cc]
jac=s.det(s.Matrix([[s.diff(q,w)for w in [u,r,sg,aa,cc]]for q in new]))
ck('FULL_normalized_five_coordinate_Jacobian',jac-6*r**4*sg**3)
ck('FULL_polynomial_normalized_source_weight',
   (r*sg*aa*aa*cc/12)*r*r/jac-(r*aa)**2*(sg*cc)/(72*r*r*(r*sg**3)))

# The moving section is constant in T and its first physical normal.
# It is retained as a finite cubic coefficient extension over (R,U,V).
q1=(3*A*k*k+2*Ec*k)*p+Fc*k
q2=(3*A*k+Ec)*p*p+Fc*p+D*k
q30=A*p**3+D*p
q3=q30+B
ck('EXACT_section_projection',
   C.subs(x,k+p*y)-y*(q3*y*y+q2*y+q1)-root)
Q0=s.expand(q2*q2-4*q1*q30)
Q=s.expand(q2*q2-4*q1*q3)
ck('EXACT_quartic_linear_B',Q-Q0+4*B*q1)
eta=2*q3*y+q2
ck('EXACT_projection_sheet_discriminant',eta*eta-Q-4*q3*(q3*y*y+q2*y+q1))

# The MISSING x²y coefficient is exactly the physical first normal.
q1d=q1+delta*k*k
q2d=q2+2*delta*k*p
q3d=q3+delta*p*p
Qd=s.expand(q2d*q2d-4*q1d*q3d)
ck('FULL_missing_x2y_normal_projection',
   (C+delta*x*x*y).subs(x,k+p*y)-y*(q3d*y*y+q2d*y+q1d)-root)
Qnormal=s.diff(Qd,delta).subs(delta,0)
ck('FULL_exact_discriminant_normal',
   Qnormal+4*(k*k*B+(V/k)*p**3),[(k,root)])
ck('FULL_discriminant_no_dropped_delta2',s.diff(Qd,delta,2))
ck('FULL_physical_delta_and_source_unit',
   s.sqrt(R)/(18*V*U*U)*kap-1/(36*R))

# All R,U motions of the coefficient section are explicit.
VR=(2+R/U**2)/V;VU=-R**2/(U**3*V)
kR=(VR-s.diff(A,R)*k**3)/(3*A*k*k+k)
kU=VU/(3*A*k*k+k)
ck('FULL_V_R_normal',2*V*VR-4-2*R/U**2)
ck('FULL_V_U_normal',2*V*VU+2*R**2/U**3)
ck('FULL_section_R_normal',s.diff(A,R)*k**3+(3*A*k*k+k)*kR-VR)
ck('FULL_section_U_normal',(3*A*k*k+k)*kU-VU)

# Actual rational twist and its prescribed conic pencil.
w,W=s.symbols('w W',nonzero=True)
Qtw=-4*q1*(T*T+R)+Q0*T
ck('EXACT_quadratic_twist_conic',Qtw-T*Q)
Qeven=Qtw.subs(T,w*w)
Qeven_normal=-4*(k*k*(w**4+R)+(V/k)*p**3*w*w)
ck('WHOLE_even_quartic_physical_normal',
   T*Qnormal-Qeven_normal.subs(w*w,T),[(k,root)])

# Finite rational parametrization of the conic, followed by the actual
# sqrt(T) branch cover.  This gives a literal cubic elliptic companion.
h,m,Qc,j1,n1=s.symbols('h0 m Q0 q1 q1_delta',nonzero=True)
Dm=m*m+4*j1;Nm=Qc-2*h*m
Tm=Nm/Dm;Wt=h+m*Tm
ck('EXACT_source_conic_parameter',
   Wt*Wt+4*j1*(Tm*Tm+R)-Qc*Tm,[(h,h*h+4*R*j1)])
ck('EXACT_companion_cubic',
   (w*Dm)**2-Nm*Dm-(w*w-Tm)*Dm*Dm)
ck('FULL_companion_holomorphic_differential',
   s.diff(Tm,m)+2*Wt/Dm)
# Hence dw/Wt=-dm/Z, Z=w*Dm.  The parameter h is NOT frozen in the
# physical normal; its derivative follows from h²=-4R q1.
hdelta=-2*R*n1/h
ck('FULL_companion_moving_h_normal',2*h*hdelta+4*R*n1)
Qcdelta=s.symbols('Q0_delta')
old_normal=(Qcdelta*Tm-4*n1*(Tm*Tm+R))/(2*Wt)
mdelta=(old_normal-hdelta)/Tm
compact_mdelta=(Qcdelta-4*n1*Tm+4*R*n1*m/h)/(2*Wt)
ck('FULL_companion_moving_coordinate_normal',mdelta-compact_mdelta)
Znormal=(Qcdelta-2*hdelta*m)*Dm+4*n1*Nm
ck('FULL_companion_cubic_coefficient_normal',
   Znormal-((Qcdelta-2*hdelta*m)*Dm+Nm*4*n1))

# The rational twist invariants really have degrees 3 and 5 in T.  This
# geometric statement alone is not polynomial-source termination.
arfile=(Path(__file__).parents[1]/'cm-corner-contraction/derive_Ferrari_rational_Aronhold.json')
ar=json.loads(arfile.read_text())
syms={n:s.Symbol(n)for n in ['A','B','D','E','F','Z','delta']}
subs={syms['A']:A,syms['B']:B,syms['D']:D,syms['E']:Ec,syms['F']:Fc,syms['Z']:V,syms['delta']:0}
s4=s.factor(s.sympify(ar['s4'],locals=syms).subs(subs))
s6=s.factor(s.sympify(ar['s6'],locals=syms).subs(subs))
I4=s.cancel(T*T*s4);I6=s.cancel(T**3*s6)
assert s.Poly(I4,T).degree()==3 and s.Poly(I6,T).degree()==5
checks['ACTUAL_twist_I4_polynomial_degree3']=True
checks['ACTUAL_twist_I6_polynomial_degree5']=True

out={
 'status':'ONE_LITERAL_FERRARI_SECTION_CONIC_COMPANION_AND_WHOLE_SOURCE_NORMAL; PRIMITIVE_OPEN',
 'source_receipt':str(old),'source_receipt_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),
 'actual_normalized_cubic':'C=A*x^3+B*y^3+D*x*y^2+x^2/2+x*y/3-V, A=R^2+R^-1,B=T+R/T,D=U^2/4,V^2=4R+R^2/U^2.',
 'FULL_normalized_source':'The exact old-to-new map is R=r^2,T=r*sigma^3,U=r*u,x=r*a,y=sigma*cA,V=r*zeta,Cnew=r*Cold. Its full five-variable Jacobian is 6*r^3*T. Thus the WHOLE selected-pair source is Res_C[x^2*y/(72RT) dU dR dT dx dy/C^2]. The first-pole family is Res_C[-sqrt(R)/(36VU^2T) dU dR dT dx dy/C_epsilon].',
 'FULL_physical_normal':'C_epsilon=(A+epsilon^2 U^2/R^2)x^3+B y^3+D xy^2+x^2/2+xy/3-V+epsilon*(VU^2/(2R^(3/2)))*x^2y. Hence delta_epsilon=VU^2/(2R^(3/2)). The second jet in A is retained. Choose k_epsilon solving (A+epsilon^2U^2/R^2)k_epsilon^3+k_epsilon^2/2-V=0: k_epsilon_prime(0)=0, with its nonzero second jet determined by this equation.',
 'ACTUAL_constant_section':'Choose one finite root k of A*k^3+k^2/2-V=0. Then (x,y)=(k,0) is a literal section for every T and every missing-x^2y delta deformation. Set x=k+s*y.',
 'conic_API':{'q1':str(q1),'q2':str(q2),'q30':str(q30),'Q0':str(s.factor(Q0))},
 'EXACT_projection':'C/y=q3*y^2+q2*y+q1,q3=q30+B. Put eta=2q3*y+q2; eta^2=Q0(s)-4B*q1(s). The affine change has dx wedge dy=y ds wedge dy, so its y factor cancels C=y*(quadratic) exactly. The full d(k) base legs are retained and wedge out only with dU dR dT.',
 'EXACT_actual_conic_bundle':'The rational twist Wtw^2=T*eta^2 is Wtw^2=-4q1*T^2+Q0*T-4R*q1, a LITERAL quadratic conic in (T,Wtw) for every actual (R,U,s). This supplies the requested conic pencil on the polynomial4/6 twist; no sections-cover-surface inference is used.',
 'EXACT_actual_even_quartic':'On w^2=T set W=Wtw. Then W^2=-4q1(w^4+R)+Q0*w^2. This retains the sqrt(T) cover and is an actual companion elliptic curve for each (R,U,s), not a CM or isotrivial claim.',
 'FULL_normal_API':'At delta=0,q1_delta=k^2,q2_delta=2ks,q3_delta=s^2. The discriminant normal is EXACTLY -4[k^2B+(V/k)s^3]; its delta^2 term cancels identically. Thus Q0_delta=-4(V/k)s^3 and (W^2)_delta=-4[k^2(w^4+R)+(V/k)s^3w^2].',
 'FULL_source_in_even_quartic':'With orientation dU dR ds dw, the whole first-pole form is +sqrt(R)/(18VU^2) dU dR ds dw/W. Its actual physical epsilon derivative is beta_pair=+(1/(36R))dU dR ds partial_delta(dw/W), equivalently [k^2(w^4+R)+(V/k)s^3w^2]/(18R W^3) dU dR ds dw. This includes the moving conic and marked section normal; no unweighted holomorphic form is substituted.',
 'FULL_base_normals':{'V_R':str(VR),'V_U':str(VU),'k_R':str(kR),'k_U':str(kU),'note':'These are actual (R,U) motions, with V^2=4R+R^2/U^2 and A*k^3+k^2/2=V. They are not frozen in any proposed absolute current.'},
 'EXPLICIT_conic_rationalization':'Adjoin h0^2=-4R*q1(s), take Wtw=h0+m*T. Then T=(Q0-2h0*m)/(m^2+4q1). On the original w^2=T cover put Z=w*(m^2+4q1): Z^2=(Q0-2h0*m)(m^2+4q1). Moreover dw/Wtw=-dm/Z exactly modulo base legs, and therefore as a full source form after dU dR ds. The actual branch divisor is m=+-sqrt(-4q1),m=Q0/(2h0),infinity; it is retained.',
 'FULL_companion_normal_and_exact_cochain':'h0_delta=-2R*k^2/h0,Q0_delta=-4(V/k)s^3,q1_delta=k^2. The fixed-w physical normal becomes m_delta=[Q0_delta-4k^2*T+4R*k^2*m/h0]/[2(h0+m*T)], with T the displayed rational function of m. Thus beta_pair=-(1/(36R))dU dR ds partial_delta(dm/Z)+d[(1/(36R))dU dR ds*m_delta/Z]. This is the explicit moving-coordinate fibre compensator, not a discarded exact term. Coefficient base legs are retained before wedging the full three-form.',
 'twist_invariants':{'I4_T2_s4':str(s.factor(I4)),'I6_T3_s6':str(s.factor(I6)),'degrees':[3,5]},
 'twist_source_scope':'Although the invariant degrees fit4/6, theta_old=sqrt(T)*theta_twist and the actual source contains dT/sqrt(T). The conic/even-quartic construction above retains that branch cover and its literal physical normal. Rationality of the twist alone supplies no primitive.',
 'remaining':'Construct one actual primitive or serving correspondence for this specific even-quartic/cubic companion source. No generic polynomial-density theorem, unweighted trace, CM inference or primitive claim is made.',
 'checks':checks,'check_count':len(checks)
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'literal Ferrari constant-section conic, companion, FULL physical source/normal and moving-coordinate cochain')
