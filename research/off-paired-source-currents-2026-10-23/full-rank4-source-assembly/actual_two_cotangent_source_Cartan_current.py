"""Canonical ACTUAL two-cotangent source current with full divergence remainder.

The coefficients are uniquely forced by the actual residual holomorphic row.
Both second-kind cotangents and every source-weight derivative are retained.
This is a positive whole-current identity, not a certificate or cancellation.
"""
from pathlib import Path
import json,time,flint
st=time.time()
import importlib.util
libpath=Path(__file__).parents[1]/'lib/native_source_field.py'
spec=importlib.util.spec_from_file_location('packet_native_source',libpath)
_native=importlib.util.module_from_spec(spec);spec.loader.exec_module(_native)
ns0=vars(_native)
W=ns0['W'];E2=ns0['E2']
R,D,a,V,A,kS,L,M,K,LR,La,MR,Ma,f0,B=[ns0[z]for z in ('R','D','a','V','A','kS','L','M','K','LR','La','MR','Ma','f0','B')]
native=ns0['ns'];vR=native['vR'];va=native['va']
gamma_mass=B(vR)+va.diff(2)-vR*(kS+1/(2*R))
normal_K=vR*B(K)+va*K.diff(2)
gamma=gamma_mass+normal_K/K
ln=W(E2(1)/3,1,-2);q=W(a/6,1,-2);ell=W(L,0,-1)
p=ln*W(f0);h=ell+3*q*q;a0=3*q*q-ell
R1=p.dl()-(q*p).dm();I1=q.dl()-q*q.dm()
u=3*q*R1/(ln*h)+3*a0*p*I1/(ln*h*h)
v=3*R1/(ln*h)+18*q*p*I1/(ln*h*h)
def Nbase(z):
    z=W(z)
    return W(vR*z.Bcoef()+va*z.z.diff(2),z.ar,z.bs)
cl=Nbase(u)+W(gamma)*u
cn=Nbase(v)+W(gamma)*v
checks={
 'actual_forced_u_serves_hol0':not bool(ln*(a0*u+2*q*ell*v)-3*(q*R1+p*I1)),
 'actual_forced_v_serves_hol1':not bool(ln*(-6*q*u+a0*v)+3*R1),
 'actual_normal_base_ell':not bool(Nbase(ell)+6*q*ln),
 'actual_normal_base_mu':not bool(Nbase(W(M,-1,0))-a0*ln),
 'actual_source_CMmass_divergence':not bool(native['rho']+f0*gamma_mass),
 'actual_canonical_volume_divergence':not bool(W(gamma)-(-6*q*ln).dl()-(a0*ln).dm()),
 'actual_forced_marked_acceleration_coefficient':not bool(ln*h*(q*v-u)-3*p*I1),
}
# Independent literal four-coordinate derivative with arbitrary source jets.
# This verifies the entire Cartan current before substituting native fields.
import sympy as S
ll,mm,xx=S.symbols('ell mu X')
qf=S.Function('q')(ll,mm);nf=S.Function('lambda_n')(ll,mm)
uf=S.Function('u')(ll,mm);vf=S.Function('v')(ll,mm)
gg=xx**3+ll*xx+mm;ff=gg*gg-4;gp=3*xx*xx+ll
bb=xx*xx/2+ll/3;aa=3*qf*qf-ll;ww=uf*xx+vf*bb
nl=-6*qf*nf;nm=aa*nf
j1=gp*ww*nl;j2=-gp*ww*nm;j3=nf*ww*(gp-3*(xx-qf)**2)
gam=S.diff(nl,ll)+S.diff(nm,mm)
cL=nl*S.diff(uf,ll)+nm*S.diff(uf,mm)+gam*uf
cN=nl*S.diff(vf,ll)+nm*S.diff(vf,mm)+gam*vf
g0=nf*(aa*uf+2*qf*ll*vf);g1=nf*(-6*qf*uf+aa*vf)
whole=-(S.diff(j1,ll)*ff-j1*gg*xx)+(S.diff(j2,mm)*ff-j2*gg)-(S.diff(j3,xx)*ff-j3*gg*gp)
expected=(g0+g1*xx)*ff-gp*(cL*xx+cN*bb)*ff
checks['WHOLE_literal_absolute_four_coordinate_current']=S.expand(whole-expected)==0
assert all(checks.values()),checks
pt=[flint.fmpq(1,4),flint.fmpq(1,36),flint.fmpq(1),flint.fmpq(1)];vv=flint.fmpq(5,4)
def point(z):
    z=W(z);return {'coefficient':str(z.z.at(pt,vv)),'r_power':z.ar,'S_power':z.bs}
out={
 'status':'EXACT_ACTUAL_SOURCE_FORCED_TWO_COTANGENT_CARTAN_CURRENT_WITH_FULL_TWO_PAIR_DIVERGENCE_REMAINDER; NO_COMPLETION',
 'checks':checks,'check_count':len(checks),
 'actual_definitions':'q=x0=a*r/(6S²),lambda_n=r/(3S²),p=lambda_n*f0,T=ell+3q²=(D+a/3)/S,R1=Dell p−Dmu(qp),I1=(Dell−qDmu)q. Actual f0=1/(72y²K),qc²=4+y².',
 'actual_source_row':'g0=3(qR1+pI1),g1=−3R1,gj3=gj4=0. This is the exact full residual holomorphic row after the actual source alpha-lambda integration by parts.',
 'forced_weights':'u=3qR1/(lambda_n T)+3(3q²−ell)pI1/(lambda_n T²),v=3R1/(lambda_n T)+18qpI1/(lambda_n T²). The determinant is lambda_n²*T², not a chosen support or degree window.',
 'normal':'N=lambda_n*(−6q Dell+(3q²−ell)Dmu+D_X),N(y)=0. Its actual base part is vR*B+va*D_a with the forward source normal from actual_SU3_source_density_continuity.',
 'gamma':'gamma_can=div_(dell dmu)(N_base)=B(vR)+va_a−(kS+1/(2R))*vR+[vR*B(K)+va*K_a]/K. The final K term is compulsory because Omega pulls back with K/(S*r). Separately gamma_mass=gamma_can−Nbase(K)/K and rho=−f0*gamma_mass; that CM-density identity may not replace gamma_can in this current.',
 'whole_absolute_cotangents':'lambda=−X*dlog[(g+Y)/2],nu=−(X²/2+ell/3)*dlog[(g+Y)/2],g=X³+ellX+mu,Y²=g²−4.',
 'normal_cotangent_transgression':'Put Bx=X²/2+ell/3,Ajet=3lambda_n*(X−q)²/Y. Then L_N(lambda)+d(X*Ajet)=lambda_n*[(3q²−ell−6qX)dX−X*dell−dmu]/Y; L_N(nu)+d(Bx*Ajet)=lambda_n*[((3q²−ell)X+2qell)dX+q²*dell+(2q−X)*dmu]/Y. All absolute base and endpoint legs are retained.',
 'whole_current':'Omega=dy*dell*dmu,W=uX+v*(X²/2+ell/3). J_N=−(gprime*W/Y)*i_N(Omega*dX)−Omega*3lambda_n*(X−q)²*W/Y. This is a fully rational three-current with no X=q pole; its T denominators are retained.',
 'whole_identity':'Omega*(g0*omega0+g1*omega1)=dJ_N−Omega*(C_lambda*lambda+C_nu*nu),C_lambda=N_base(u)+gamma*u,C_nu=N_base(v)+gamma*v. Both second-kind rows and ALL derivatives of u,v,lambda_n,q are retained.',
 'FULL_rank4_remainder':'With eta4=(X4+ellX²+muX/2)dX/Y, T=dJ_N+Omega*[(ell²*C_nu/3)*omega0+(ell*C_lambda−3mu*C_nu/4)*omega1+3C_lambda*omega3+(3C_nu/2)*eta4]. Both secondkind components are explicit and nonzero.',
 'u':u.data(),'v':v.data(),'C_lambda':cl.data(),'C_nu':cn.data(),
 'actual_point':{'R':'1/4','D':'1/36','a':'1','V':'5/4','u':point(u),'v':point(v),'C_lambda':point(cl),'C_nu':point(cn)},
 'remainder_zero':not bool(cl) and not bool(cn),
 'marked_source_bridge':'lambda_n*T*(qv−u)=3pI1 EXACT. Thus u*Qpull(L_N lambda)+v*Qpull(L_N nu)=(3pI1/T)*dlogzQ, but the full normal inversion includes the compulsory base1leg (lambda_n/Y)*[(−uX+v*q²)dell+(−u+v*(2q−X))dmu]. At Q this equals (3pI1/T)*betaQ/YQ. It vanishes only after the original Omega wedge, so it must be restored before any marked CM pullback. This is an actual coefficient identity, not a source primitive.',
 'finitecharge_guard':'No mixed X=q pole is introduced by this Cartan current. It is only a full two-cotangent gauge unless its displayed two-pair divergence remainder is served. Inserting CM currents requires their literal source coefficient and all weight derivatives; no cancellation from a bare CM trace follows.',
 'normal_mark_guard':'N acts on the epsilon-zero canonical base functions q and lambda_n through the inverse moduli map. Physical zero-mark epsilon motion has an additional explicit family contribution, so evaluating L_N(lambda/nu) at Q is not interchangeable with differentiating the pre-evaluated physical lambda_Q/nu_Q without that moving-section commutator.',
 'elapsed_seconds':round(time.time()-st,3)
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual sourceweights, full normal and divergence; pair remainderzero?',out['remainder_zero'],'seconds',round(time.time()-st,3),flush=True)
print('point C_lambda',out['actual_point']['C_lambda'],'C_nu',out['actual_point']['C_nu'],flush=True)
