"""Actual source density -> heat -> two-cotangent row, with all mass units.

This closes the reproducible binding chain, not the physical residual.
It extracts only the positive prefix identity from the original CM adjoint
producer; the unrelated one-candidate comparison is deliberately omitted.
"""
from pathlib import Path
import importlib.util,json
p=Path(__file__).parent/'lib/native_source_field.py'
spec=importlib.util.spec_from_file_location('packet_heat_source',p)
n=importlib.util.module_from_spec(spec);spec.loader.exec_module(n)
W,E2=n.W,n.E2
q=W(n.a/6,1,-2);ln=W(E2(1)/3,1,-2);p0=ln*W(n.f0)
R1=p0.dl()-(q*p0).dm();I1=q.dl()-q*q.dm()
Aheat=p0.dl().dl()-2*(q*p0).dm().dl()+(q*q*p0).dm().dm()
sigma=-W(n.rho).dm()
checks={
 'actual_source_forcing_equals_full_L0_prefix_plus_heat':not bool(sigma+p0.l0()-3*Aheat),
 'actual_heat_is_covariant_density_divergence':not bool(Aheat-R1.dl()+(q*R1+p0*I1).dm()),
 'actual_nonzero_acceleration':bool(I1),
}
assert all(checks.values()),checks
out={
 'status':'EXACT_ACTUAL_SOURCE_TO_HEAT_AND_TWO_COTANGENT_ROW_BINDING; FULL_REMAINDER_OPEN',
 'checks':checks,'check_count':len(checks),
 'physical_source':'f0=1/(72y^2K),rho=−Dell(f0*ell_delta)−Dmu(f0*mu_delta),sigma=−Dmu rho. Physical N is already absorbed; the preceding whole conic Cartan/continuity replays fix this source.',
 'prefix':'p=lambda_n*f0,q=x0,lambda_n=r/(3S^2). sigma=−L0(p)+3Aheat EXACT with full source, r,S,V,K derivatives. The exact L0 Green current and rational endpoint fiber cochains are in actual_SU3_PF_Green_current.py/json.',
 'full_covariant_heat_identity':'Aheat*dell*dmu=d[alpha],alpha=R1*(dmu+q*dell)+p*I1*dell,R1=Dell(p)−Dmu(qp),I1=(Dell−qDmu)q. The second term is compulsory and nonzero.',
 'full_heat_to_source_row':'With Omega=dy*dell*dmu and lambda=−X*dlogz, dlambda=dell*omega1+dmu*omega0: 3Aheat*Omega*lambda=d[−3dy*alpha*lambda]+Omega*(g0*omega0+g1*omega1),g0=3(qR1+pI1),g1=−3R1. This is exactly the row served by the included two-cotangent Cartan current; its C_lambda,C_nu remainder is retained.',
 'scope':'No scalar particular solution, CM source intertwiner, global boundary primitive, legal denominator, or sextic certificate is asserted.'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual whole source/heat/cotangent-row binding; all remaining costs retained')
