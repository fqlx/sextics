"""Exact SU(3) scalar-PF Green current INCLUDING literal fibre cochains.

The universal construction is ready to pull back an ACTUAL source-specific
adjoint identity. It does not assert existence of that identity.
"""
from pathlib import Path
import sympy as S,json,time
st=time.time();x,l,m=S.symbols('x ell mu',nonzero=True)
g=x**3+l*x+m;F=3*x*x+l;ff=g*g-4;B=2*l*x+3*m
checks={}
def ck(n,z):
 checks[n]=S.cancel(S.expand(z))==0
 assert checks[n],(n,S.cancel(z))
# Every odd form/scalar is represented as r/y,y²=ff; these operators
# differentiate the ACTUAL algebraic y as well as every rational coefficient.
def Do(r,v):return S.diff(r,v)-r*S.diff(ff,v)/(2*ff)
def Eo(r):return 2*l*Do(r,l)+3*m*Do(r,m)
def L0o(r):return 3*Do(Do(r,l),l)+l*Do(Do(r,m),m)
def L2o(r):return Eo(Eo(r))-2*Eo(r)+r-36*Do(Do(r,m),m)
r=-x*F
C0=1+x*g*F/ff
C2=x*g*(B*B-36)/ff-x*(3*x**3+5*l*x+9*m)
ck('L0_SW_LITERAL_fibre_cochain',L0o(r)-Do(C0,x))
ck('L2_SW_LITERAL_fibre_cochain',L2o(r)-Do(C2,x))
ck('SW_mu_to_hol0_WITH_exact_fibre_term',Do(r,m)-1+Do(x,x))
ck('SW_ell_to_hol1_WITH_exact_fibre_term',Do(r,l)-x+Do(x*x,x))
# Literal ABSOLUTE SW form=-x*dlogz, not its relative dx representative.
# The extra base legs of Li(lambda_abs)-dCi are recorded, not erased.
absn=[r,-x*x,-x]
base_remainders={}
for name,op,C in [('L0',L0o,C0),('L2',L2o,C2)]:
 vals=[S.cancel(op(absn[i])-Do(C,v))for i,v in enumerate((x,l,m))]
 ck(name+'_ABSOLUTE_dx_component',vals[0])
 base_remainders[name]={'dell_numerator_over_y':str(S.factor(vals[1])),'dmu_numerator_over_y':str(S.factor(vals[2]))}
ck('L0_absolute_base_normal_retained',L0o(-x)-Do(C0,m)-g/ff)
# Universal exact variable-coefficient Green identities; no endpoint equation
# is used here, so this check also retains ALL coefficient derivatives.
u=S.Function('u')(l,m);v=S.Function('v')(l,m)
E=lambda q:2*l*S.diff(q,l)+3*m*S.diff(q,m)
L0=lambda q:3*S.diff(q,l,2)+l*S.diff(q,m,2)
L2=lambda q:E(E(q))-2*E(q)+q-36*S.diff(q,m,2)
L2adj=lambda q:E(E(q))+12*E(q)+36*q-36*S.diff(q,m,2)
j0=[3*(v*S.diff(u,l)-S.diff(v,l)*u),l*(v*S.diff(u,m)-S.diff(v,m)*u)]
BE=v*E(u)-(E(v)+7*v)*u
j2=[2*l*BE,3*m*BE-36*(v*S.diff(u,m)-S.diff(v,m)*u)]
ck('WHOLE_L0_variable_coefficient_Green',S.diff(j0[0],l)+S.diff(j0[1],m)-v*L0(u)+L0(v)*u)
ck('WHOLE_L2_variable_coefficient_Green',S.diff(j2[0],l)+S.diff(j2[1],m)-v*L2(u)+L2adj(v)*u)
# Explicit zero-order/first-order terms confirm the formal adjoint's measure.
ck('canonical_measure_E_formal_adjoint_divergence',S.diff(2*l,l)+S.diff(3*m,m)-5)
assert all(checks.values())
out={'status':'EXACT_SU3_PF_GREEN_CURRENT_WITH_FIBRE_COCHAINS; ACTUAL_SOURCE_ADJOINT_IDENTITY_STILL_REQUIRED',
'checks':checks,'check_count':len(checks),
'actual_normalized_curve':'y²=(x³+ell*x+mu)²−4; z=(x³+ell*x+mu+y)/2; lambda_abs=−x*dlogz,lambda_rel=−x*(3x²+ell)*dx/y. Constant4 is the actual normalized scale; all physical variable-scale/finite-branch units must remain in the pullback/source coefficient.',
'PF_operators':'L0=3D_ell²+ellD_mu². E=2ellD_ell+3muD_mu; L2=(E−1)²−36D_mu². Both annihilate the FULL rank4 SW period module; no nilpotence or rank1 projection is assumed.',
'formal_adjoints_canonical_volume':'L0*=L0; L2*=(E+6)²−36D_mu². E* =−E−5 with respect to d_ell d_mu; the +6 and Green +7 terms are compulsory.',
'literal_fibre_C0':'C0=1/y+x*g*F/y³,g=x³+ell*x+mu,F=3x²+ell; L0(lambda_rel)=d_x C0.',
'literal_fibre_C2':'C2=x*g*((2ell*x+3mu)²−36)/y³−x*(3x³+5ell*x+9mu)/y; L2(lambda_rel)=d_x C2.',
'full_absolute_base_remainders':base_remainders,
'base_normal_guard':'Li(lambda_abs)=dCi+the recorded dell/dmu legs. They vanish only after the actual top-moduli wedge. The Green current below uses lambda_rel=literal scalar*dx and includes Ci; after physical pullback dx moves and ALL its base legs are automatically retained. Do not substitute Li(lambda_abs)=dCi without these corrections.',
'Green_flux_L0':'For endpoint-independent f, jell=3(f*D_ell(lambda_rel)−D_ell(f)*lambda_rel),jmu=ell*(f*D_mu(lambda_rel)−D_mu(f)*lambda_rel). Entries are literal fibre1forms.',
'Green_flux_L2':'BE=f*E(lambda_rel)−(E(f)+7f)*lambda_rel; jell=2ell*BE,jmu=3mu*BE−36*(f*D_mu(lambda_rel)−D_mu(f)*lambda_rel). All derivatives of f,including actual branch/source units, are retained.',
'complete_current_3base':'Let spectator coordinate s be fixed by D_ell,D_mu,Omega3=ds*dell*dmu. Write ji=ji_scalar*dx and Flux_i=i_(ji_scalar*partial_i)(Omega3)*dx. Then dFlux=Omega3*[f*Li(lambda_rel)−Li*(f)*lambda_rel]. The exact primitive is J_i=−Flux_i−Omega3*f*Ci, so dJ_i=Omega3*Li*(f)*lambda_rel. Every cochain derivative is literal; ds/base terms that wedge out do so against Omega3.',
'holomorphic_source_conversion':'omega0=dx/y=D_mu(lambda_rel)+d_x(x/y),omega1=x dx/y=D_ell(lambda_rel)+d_x(x²/y). For actual source Omega3*(g0*omega0+g1*omega1), define firstorder flux Vhol=(g1*lambda_scalar)*partial_ell+(g0*lambda_scalar)*partial_mu and Jhol=i_Vhol(Omega3)*dx−Omega3*(g0*x+g1*x²)/y. Then source=dJhol+Omega3*[−D_mu(g0)−D_ell(g1)]*lambda_rel.',
'ACTUAL_certificate_interface':'If an actual rational source-specific identity −D_mu(g0)−D_ell(g1)=L0*(f0)+L2*(f2) holds on the complete physical finite base field (fixed spectator s, with all algebraic branch derivatives), then J=Jhol+J_0[f0]+J_2[f2] is a literal rational primitive of the ENTIRE source. Add the separately recorded parent Cartan and moving-map cochains, then perform lawful finite trace. No inference from coprime modules/Ore Bezout alone is permitted.',
'physical_source_density_guard':'For s=XQ or another actual marked coordinate, put EVERY physical Jacobian,1/YQ,N,variable scale and source unit into g0,g1 BEFORE differentiating. If a different base measure is used, conjugate the adjoints by its full density or absorb it into the coefficients; do not keep canonical adjoints while silently dropping that density. Endpoint-dependent f would add C_i*D_x(f) terms and is outside this stated interface.',
'open':'No source-specific adjoint f0,f2 has been constructed here. The current construction and all fibre cochains are exact and ready for one actual adjoint identity; no certificate is claimed.',
'elapsed_seconds':round(time.time()-st,3)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'literal PF fibrecochains,absolute normals,and exact Green currents;',round(time.time()-st,3),'seconds')
