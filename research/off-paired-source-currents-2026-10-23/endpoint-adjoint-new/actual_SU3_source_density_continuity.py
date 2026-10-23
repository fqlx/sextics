"""Independent exact actual conic-mark source/adjoint-forcing binding.

Verifies the entire variable-scale/branch-density continuity equation before
any attempt to solve the source-specific adjoint PF identity.
"""
from pathlib import Path
import json,time
st=time.time()
import importlib.util
libpath=Path(__file__).parents[1]/'lib/native_source_field.py'
spec=importlib.util.spec_from_file_location('packet_native_continuity',libpath)
_native=importlib.util.module_from_spec(spec);spec.loader.exec_module(_native)
ns=vars(_native)
E2=ns['E2'];R,D,a,V,A,kS,L,M=[ns[z]for z in ('R','D','a','V','A','kS','L','M')]
def B(z):return E2(z).diff(0)+E2(D/R)*E2(z).diff(1)
LR=B(L)-kS*L;La=L.diff(2)
MR=B(M)-M/(2*R);Ma=M.diff(2)
K=Ma*LR-E2(La)*MR
LD=-a/(3*A)
MD=-D/(3*A)-a/(9*A)+a*a/(18*A*A)
Kd=E2(MD.diff(2))*LR+Ma*(B(LD)-kS*LD)-E2(LD.diff(2))*MR-E2(La)*(B(MD)-MD/(2*R))
vR=(E2(LD)*Ma-E2(La)*MD)/K
va=(LR*MD-MR*LD)/K
f0=E2(D/(18*R))/K # 1/(72*y²*K),actualy²=R/(4D)
rho=E2(D/(18*R))*(vR*B(K)+va*K.diff(2)-Kd)/(K*K)
# Ell_delta=LD/S and mu_delta=MD/sqrtR. Canonical derivatives include
# the derivative of S^-1 and sqrtR^-1; no fixed-physical-base substitution.
fA=f0*LD;fB=f0*MD
Dell_fA=(Ma*(B(fA)-fA*kS)-MR*fA.diff(2))/K
Dmu_fB=(-E2(La)*(B(fB)-fB/(2*R))+LR*fB.diff(2))/K
checks={}
def ck(n,z):checks[n]=not bool(E2(z));assert checks[n],n
ck('actual_forward_source_normal_ell',LR*vR+E2(La)*va-LD)
ck('actual_forward_source_normal_mu',MR*vR+Ma*va-MD)
ck('WHOLE_actual_source_density_continuity',rho+Dell_fA+Dmu_fB)
divMass=B(vR)+va.diff(2)-vR*(kS+1/(2*R))
ck('independent_physical_CM_mass_Piola_normal',Kd-vR*B(K)-va*K.diff(2)-K*divMass)
ck('source_rho_is_full_CM_mass_divergence',rho+f0*divMass)
# Exact nondegenerate physical point; only a sanity record,not a closuretest.
import flint
pt=[flint.fmpq(1),flint.fmpq(1,9),flint.fmpq(1),flint.fmpq(1)];vv=flint.fmpq(5,2)
out={'status':'EXACT_ACTUAL_CONIC_MARK_SOURCE_CONTINUITY_AND_DENSITY_BINDING; PF_ADJOINT_SOLUTION_OPEN',
'checks':checks,'check_count':len(checks),
'actual_source':'spectatory=YQc=sqrtR/U, y²=R/(4D). Actual physical firstpole base densityf0=1/(72*y²*K) inorientationdell*dmu*dy*omega0(P). Physical N is already absorbed in this density; it is not discarded.',
'actual_moduli':'ell=L/S,mu=M/sqrtR,S³=R³+1,L=D+a/3−a²/(12A),M=−aL/(6A)−(V+1/(216A²))a³,A=(R³+1)/R. Physical B=∂R+(D/R)∂D,includingB(V)=V/(2R),holdsyfixed.',
'actual_normal':'ell_delta=LD/S,mu_delta=MD/sqrtR,LD=−a/(3A),MD=−D/(3A)−a/(9A)+a²/(18A²). ForwardvR=(LD*Ma−La*MD)/K,va=(LR*MD−MR*LD)/K. Inversefixedtargetmotion is MINUS thisforwardvector.',
'actual_K':'LR=B(L)−kS*L,MR=B(M)−M/(2R),La=L_a,Ma=M_a,K=Ma*LR−La*MR,kS=R²/(R³+1). Kdelta differentiated with the ENTIRE displayed LD/MD,bothBderivativesandsourcemassscales.',
'WHOLE_density_normal':'rho=[vR*B(K)+va*K_a−Kdelta]/(72*y²*K²). EXACTLY rho=−D_ell[f0*ell_delta]−D_mu[f0*mu_delta]. EverycanonicalpartialholdsyfixedandmovesphysicalR,D,V,a.',
'canonical_partial_operators':'D_ell=S/K*[Ma*B−MR*D_a],D_mu=sqrtR/K*[−La*B+LR*D_a]. Thus D_ell(fA/S)=[Ma*(BfA−kS*fA)−MR*fA_a]/K andD_mu(fB/sqrtR)=[−La*(BfB−fB/(2R))+LR*fB_a]/K. The two compulsory scale derivatives are included.',
'CM_mass_identity':'f0*dell*dmu=dR*da/[72*y²*S*sqrtR]=−omegaCM*da/(72*y²),omegaCM=dXE/YE=−dR/(SsqrtR). ExactdivMass=B(vR)+va_a−(kS+1/(2R))*vR givesrho=−f0*divMass. This independently confirms the actual scalar forcingbeforePFadjointconstruction.',
'Green_binding':'InactualorientationOmega3=dy*dell*dmu,holsourceOmega3*rho*omega0 reduces bytheEXACTcurrentinactual_SU3_PF_Green_current.py/json toforcing−D_mu(rho)*lambdaSW. A source-specific identity−D_mu(rho)=L0*(fA)+L2*(fB) would produce a whole rational current with its fibercochains. Such fA,fB are NOT asserted here.',
'exact_point_f0':str(f0.at(pt,vv)),'exact_point_rho':str(rho.at(pt,vv)),
'open':'Freshalgebraicowns actual CM-source adjoint identity. These continuity/Piola identities are positiveactualsourcebindingchecks,not genericexactness,an Oreterminationclaim,or a certificate.',
'elapsed_seconds':round(time.time()-st,3)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'WHOLE actual SU3 source/density/CMmass continuity;',round(time.time()-st,3),'seconds')
