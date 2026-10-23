"""Independent physical audit: lawful weighted CM current and BOTH SW channels.

The normalized lambda current is checked in original R,a,V,hQ coordinates.
The second cotangent nu has a distinct CM quotient and exact/moving-normal
cochains.  No whole 3Aheat primitive is inferred from these ingredients.
"""
from pathlib import Path
import sympy as s,json
R,a,V,hQ=s.symbols('R a V hQ',nonzero=True)
S3=R**3+1;Delta=S3*S3-R*R*V*V*a**6;hf=V*V*a**6-4*R
coords=(R,a,V);checks={}
def red(v):
    n=s.cancel(v).as_numer_denom()[0]
    return s.factor(s.rem(n,hQ*hQ-hf,hQ))
def ck(n,v):checks[n]=red(v)==0;assert checks[n],(n,red(v))
def dd(v,i):return s.diff(v,coords[i])+s.diff(v,hQ)*s.diff(hf,coords[i])/(2*hQ)
# Derived directly from lambda_n/b times the two source-bound elliptic maps.
# The dV component comes from db/b=dV/(3V)-dR/(6R), not from a fixed b.
J=[-2*V*a**4*hQ*R**2/(3*S3*Delta)+2*V*a**4*(1-R**3)/(9*hQ*Delta),
   -4*R*V*a**3*(1-R**3)/(3*hQ*Delta),
   -4*R*a**4*(1-R**3)/(9*hQ*Delta)]
log=[s.Rational(2,3)/R-2*R*R/S3,0,-1/(3*V)]
source=[-2*V*a**3/(3*S3*hQ),-2*a**4/(9*S3*hQ),0]
raw=json.loads((Path(__file__).parents[1]/'source-carrying-construction/actual_zero_mark_weighted_CM_current.json').read_text())
for i in range(3):
    ck('independent_physical_current_match_'+str(i),J[i]-s.sympify(raw['rational_current_RaV'][i],locals=locals()))
    ck('actual_Qodd_character_'+str(i),J[i].subs(hQ,-hQ)+J[i])
for n,(i,j) in enumerate(((0,1),(0,2),(1,2))):
    ck('FULL_absolute_source_and_weight_'+str(i)+str(j),dd(J[j],i)-dd(J[i],j)-source[n]-(log[i]*J[j]-log[j]*J[i]))
Jregular=[-2*V*hQ*a**4*R**2/(3*S3*Delta),
          V*hQ*a**3*(1-R**3)/(3*Delta),
          a**4*hQ*(1-R**3)/(9*Delta)]
Jh=-V*a**4*(1-R**3)/(9*Delta)
for i in range(3):
    ck('actual_hQ_ramification_regular_rewrite_'+str(i),Jregular[i]+Jh*s.diff(hf,coords[i])/(2*hQ)-J[i])
cost=(1/(2*R)-2*R*R/S3)*J[1]
expected=2*V*a**3*(1-R**3)*(3*R**3-1)/(3*S3*hQ*Delta)
ck('source_I1_acceleration_cost_exact_unit',cost-expected)
# The marked second SW cotangent is reduced on its ACTUAL norm curve.
aa,qc,b,gamma,YQ,ln,SS,DD=s.symbols('aa qc b gamma YQ lambda_n S D',nonzero=True)
norm=qc*qc*aa**6-4
def nr(v):
    n=s.cancel(v).as_numer_denom()[0]
    n=s.rem(n,YQ*YQ-norm,YQ)
    n=s.rem(n,b**3-qc,b)
    return s.factor(s.rem(n,gamma**3-16,gamma))
def nc(n,v):checks[n]=nr(v)==0;assert checks[n],(n,nr(v))
def nda(v):return s.diff(v,aa)+s.diff(v,YQ)*3*qc*qc*aa**5/YQ
def ndq(v):return s.diff(v,qc)+s.diff(v,YQ)*qc*aa**6/YQ+s.diff(v,b)*b/(3*qc)
XB=gamma/(b*b*aa*aa);YB=2*s.I*YQ/(qc*aa**3)
nc('actual_SECOND_CM_quotient',YB*YB-XB**3+4)
etaB=[s.cancel(XB*nda(XB)/YB),s.cancel(XB*ndq(XB)/YB)]
etaA=[2*b**4*aa**3/YQ,s.Rational(2,3)*b*aa**4/YQ]
F=3*YQ/(2*qc*aa)
Ab=[3*qc*aa**4/YQ,aa**5/YQ]
for i,der in enumerate((nda,ndq)):
    nc('FULL_other_CM_Hermite_'+str(i),Ab[i]-der(F)-6*s.I*b*etaB[i]/(gamma*gamma*qc)-(YQ/(qc*qc*aa) if i else 0))
# nuQ=-(x0²/2+ell/3)dlogzQ, x0=a*ln/2, ell=TQ-3x0².
TQ=(DD+aa/3)/SS
nu_coeff=TQ/3-aa*aa*ln*ln/8
dlz=[-3*qc*aa*aa/YQ,-aa**3/YQ]
for i,der in enumerate((nda,ndq)):
    dec=-DD*dlz[i]/(3*SS)+etaA[i]/(6*SS*b)-ln*ln*der(F)/8-3*s.I*b*ln*ln*etaB[i]/(4*gamma*gamma*qc)-(ln*ln*YQ/(8*qc*qc*aa) if i else 0)
    nc('FULL_nuQ_two_CM_channels_'+str(i),-nu_coeff*dlz[i]-dec)
out={
 'status':'PASS_INDEPENDENT_PHYSICAL_WEIGHTED_CM_CURRENT_AND_FULL_SECOND_COTANGENT_CM_QUOTIENT; SOURCE_HEAT_BRIDGE_OPEN',
 'checks':checks,'check_count':len(checks),
 'weighted_current':'Jphys=(lambda_n/b)K_RA, fully rational R,a,V,hQ. Its source, entire dlog(lambda_n/b) weight cost and all dV terms match sourceagent independently. The ordinary hQ trace is zero; the Qodd genus2 heat/kernel factor remains necessary.',
 'branch_regularity':'The current also equals a one-form with coefficients divisible by hQ in dR,da,dV,dhQ, using dhQ=d(V²a6−4R)/(2hQ). Thus its apparent hQ=0 pole is removable away from S3*Delta=0; all collisions/infinity strata remain in the proper-divisor audit.',
 'exact_acceleration_unit':'At fixed actual y, cost=2Va³(1−R³)(3R³−1)/(3S3 hQ Delta)=8rSK(1−R³)I1/(3hQDelta). It is not equal to alpha acceleration pI1*dell without the remaining physical coframe/unit.',
 'actual_SECOND_CM_map':'b³=qc,gamma³=16,XB=gamma/(b²a²),YB=2iYQ/(qc*a³),YB²=XB³−4. This is the other elliptic quotient of the even norm curve YQ²=qc²a6−4, not a generic endpoint factor.',
 'full_secondkind_reduction':'Let F=3YQ/(2qc*a),etaB=XB*dXB/YB. EXACT (3qc*a4 da+a5 dqc)/YQ=dF+[6i*b/(gamma² qc)]etaB+YQ*dqc/(qc²*a). Every spectator dqc leg is retained.',
 'FULL_nuQ_factor':'nuQ=−D*dlogzQ/(3S)+etaA/(6S*b)−lambda_n²*dF/8−[3i*b*lambda_n²/(4gamma² qc)]etaB−lambda_n²*YQ*dqc/(8qc²*a). This identity contains BOTH actual CM secondkind channels plus a logarithmic norm form and exact/moving-normal pieces.',
 'exact_prefix_guard':'If −lambda_n²*dF/8 is extracted as d(−lambda_n²F/8), add +F*d(lambda_n²)/8 explicitly. The D/S,b,lambda_n coefficients also carry their full derivatives in a current.',
 'rank4_guard':'The actual physical normal has KS rank2; this nu channel is necessary alongside lambdaQ. No rank1 Schiffer reduction, unweighted CM trace or vanishing of the 3Aheat correction follows.',
 'scope':'Independent source-unit/current audit and exact second-kind factorization only. Fullrank4/sourceagent must still assemble the actual 3Aheat source with all coefficient costs and finite characters.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'full weighted CMcurrent and BOTH marked SW/CM channels')
