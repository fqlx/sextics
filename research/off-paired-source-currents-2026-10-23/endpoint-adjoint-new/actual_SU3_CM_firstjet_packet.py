"""Canonical covariant FIRST-JET packet of the actual CM mass defect.
No varied amplitudes. All source branch/scale derivatives retained.
"""
from pathlib import Path
import json,time,flint,sympy as S
st=time.time()
import importlib.util
libpath=Path(__file__).parents[1]/'lib/native_source_field.py'
spec=importlib.util.spec_from_file_location('packet_native_firstjet',libpath)
_native=importlib.util.module_from_spec(spec);spec.loader.exec_module(_native)
ns=vars(_native)
W,E2=ns['W'],ns['E2'];R,D,a,K,f0,V=[ns[z]for z in ('R','D','a','K','f0','V')]
p=W(f0/3,1,-2);x0=W(a/6,1,-2)
I1=x0.dl()-x0*x0.dm()
R1=p.dl()-(x0*p).dm()
Ic=I1.z*K;Rc=R1.z*K**3
lamn=W(E2(1)/3,1,-2)
lamdot=-W(1,1,1)*W(lamn.Bcoef(),lamn.ar,lamn.bs)
lamdotExpected=W((3*R**3-1)/6,0,-4)
Iexpected=W(V*a**3*(3*R**3-1)/(4*R*(R**3+1)**2)/K,1,2)
cmDot=lambda q:-W(1,1,1)*W(q.Bcoef(),q.ar,q.bs)
XE=W(1/R,0,2);YE=W(1-R**3,-3,0);cc=W(1,-1,1);rr=W(1,1,0)
checks={
 'actual_covariant_firstjet_simple_factor':not bool(I1-Iexpected),
 'actual_CMdual_derivative_lambda':not bool(lamdot-lamdotExpected),
 'actual_firstjet_is_CMnormal':not bool(I1-W(3*V*a**3/(2*K),-1,0)*lamdot),
 'actual_CM_source_X_dot':not bool(cmDot(XE)-YE),
 'actual_CM_source_r_log_connection':not bool(cmDot(rr)/rr+cc/2),
 'actual_CM_source_sqrtX_dot':not bool(cmDot(cc)-YE/(2*cc)),
 'actual_CM_source_lambda_covariant_connection':not bool(lamdot-(cc/2-YE/XE)*lamn),
}
# Independent universal covariant density identity, all z coefficient jets.
l,m=S.symbols('ell mu');z=S.Function('z')(l,m);pp=S.Function('p')(l,m)
Az=S.diff(pp,l,2)-2*S.diff(z*pp,l,m)+S.diff(z*z*pp,m,2)
r1=S.diff(pp,l)-S.diff(z*pp,m);i1=S.diff(z,l)-z*S.diff(z,m)
# theta=dmu+z*dell; d[R1theta+pI1dell]=(R1_l−(zR1+pI1)_mu)Omega.
identity=S.expand(Az-S.diff(r1,l)+S.diff(z*r1+pp*i1,m))
assert identity==0
checks['universal_covariant_density_identity']=True
assert all(checks.values())
# Actual native factor reconstruction for the K-cleared fields.
raw={'I1_times_K':Ic.data(),'R1_times_K3':Rc.data()}
factors={}
for tag,val in raw.items():
 factors[tag]={}
 for name,polystr in val.items():
  # RF numerator/denominator native context is inherited from the source.
  rr=Ic.x if name.startswith('even') else Ic.y
  if tag=='R1_times_K3':rr=Rc.x if name.startswith('even')else Rc.y
  poly=rr.n if name.endswith('numerator')else rr.d
  cc,ff=poly.factor()
  factors[tag][name]={'constant':str(cc),'factors':[{'polynomial':str(q),'multiplicity':int(e),'terms':len(q),'degree':int(q.total_degree())}for q,e in ff]}
out={'status':'EXACT_ACTUAL_COVARIANT_CM_FIRSTJET_PACKET; ADJOINT_CORRECTION_OPEN',
'checks':checks,'check_count':len(checks),
'actual_definitions':'p=lambda_n*f0,x0=a*r/(6S²),lambda_n=r/(3S²). Define V0=Dell−x0*Dmu,I1=V0(x0),R1=Dell(p)−Dmu(x0*p). All actualr,S,V derivatives included through canonicaltargetpartialderivatives.',
'EXACT_covariant_identity':'A*Omega=d[R1*(dmu+x0*dell)+p*I1*dell],Omega=dell*dmu,A=Dell²p−2DellDmu(x0p)+Dmu²(x0²p). The pI1 term is the covariantacceleration of the variable characteristic V0; omitting it is wrong.',
'EXACT_source_CM_normal':'I1=V*a³*(3R³−1)/(4r*S4*K). WithomegaCM=−dR/(Sr),dualCMderivativeDot=−Sr*B gives Dot(lambda_n)=(3R³−1)/(6S4),lambda_n=r/(3S²). Therefore I1=3Va³*Dot(lambda_n)/(2rK)=−3q0*Dot(lambda_n)/(2K). Theseequalitiesareindependentlyexact-checked,withallsourcer,S,Vmotions.',
'EXACT_finite_cover_CM_connection':'c=S/r=sqrtXE. DotXE=YE,Dotc=YE/(2c),Dotr/r=−c/2,andDotlambda_n=(c/2−YE/XE)*lambda_n EXACTLY. Thus (c/2)*omegaCM=−dlogr and(YE/XE)*omegaCM=dlogXE ontheactualsourcecover. This is the sourceunit covariantconnection; multiplyingitbyavaryingcoefficientstillrequiresitsfullderivativeanddoesnotitselfproveclosure.',
'I1':I1.data(),'R1':R1.data(),
'forced_pole_cleared_packet':raw,'exact_factors':factors,
'actual_remaining':'sigma=−L0*(p)+3A is exact. The single testedL2*(XE*p) is not constantproportionalto3A. This first-jet packet is the exactsource-specific remaininggeometry,not an independently chosen amplitude or a newclosureclaim.',
'elapsed_seconds':round(time.time()-st,3)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS canonical firstjetidentity; actual K/K³ packet factored',round(time.time()-st,3),'seconds')
for tag in raw:
 print(tag,[(n,[(q['terms'],q['degree'],q['multiplicity'])for q in fs['factors']])for n,fs in factors[tag].items()])
