"""Actual zero-mark CM current: normalized source, all characters and costs.

This is an audited source-bound contraction ingredient, NOT a primitive of
3*Aheat*lambdaSW.  In particular the full coefficient of the acceleration
cost is retained, and the ordinary Q-sheet trace of this ingredient is zero.
"""
from pathlib import Path
import json
import sympy as s

checks = {}
def ck(name, value):
    checks[name] = s.cancel(value) == 0
    assert checks[name], (name, s.factor(value))

# The full cyclic CM projector, rather than a representative modulo a closed
# one-form, has an exact character on both elliptic curves.
x,u,y,v = s.symbols('XR XA YR YA', nonzero=True)
den = x**3-u**3
kk = [2*u*u*v/(y*den), -2*x*u*y/(v*den)]
def ED(f, i):
    z,w = ((x,y),(u,v))[i]
    return s.diff(f,z) + s.diff(f,w)*3*z*z/(2*w)
def er(f):
    n = s.cancel(f).as_numer_denom()[0]
    n = s.rem(n,y*y-x**3+4,y)
    return s.factor(s.rem(n,v*v-u**3+4,v))
assert er(ED(kk[1],0)-ED(kk[0],1)-u/(y*v)) == 0
checks['absolute_cyclic_projector_dK_equals_omegaR_etaA'] = True
for z in (y,v):
    for k in range(2):
        assert er(kk[k].subs(z,-z)+kk[k]) == 0
checks['projector_hyperelliptic_character_R_and_A'] = True

# The source-bound normalized current J=(lambda_n/b)K has no cube roots or r,S
# left.  Here b^3=qc=V/r, r^2=R, S^3=R^3+1, and hQ=r*YQ.
R,a,V,h = s.symbols('R a V hQ', nonzero=True)
S3 = R**3+1
Delta = S3*S3-R*R*V*V*a**6
hf = V*V*a**6-4*R
coords = (R,a,V)
def PD(f,i):
    return s.diff(f,coords[i])+s.diff(f,h)*s.diff(hf,coords[i])/(2*h)
def pr(f):
    n=s.cancel(f).as_numer_denom()[0]
    return s.factor(s.rem(n,h*h-hf,h))
def pck(name,f):
    checks[name]=pr(f)==0
    assert checks[name],(name,pr(f))
J = [
    -2*V*h*a**4*R**2/(3*S3*Delta)
       +2*V*(1-R**3)*a**4/(9*h*Delta),
    -4*V*R*(1-R**3)*a**3/(3*h*Delta),
    -4*R*(1-R**3)*a**4/(9*h*Delta),
]
# lambda_n/b * omegaR wedge etaA, in R,a,V coordinates.
T = [-2*V*a**3/(3*S3*h), -2*a**4/(9*S3*h), s.Integer(0)]
# Full d log(lambda_n/b).  Its dV leg is compulsory before dy is wedged.
lg = [s.Rational(2,3)/R-2*R**2/S3, s.Integer(0), -1/(3*V)]
pairs=((0,1),(0,2),(1,2))
cost=[]
for k,(i,j) in enumerate(pairs):
    C = lg[i]*J[j]-lg[j]*J[i]
    cost.append(C)
    pck('FULL_absolute_dJ_source_plus_connection_'+str(i)+str(j),
        PD(J[j],i)-PD(J[i],j)-T[k]-C)
for i in range(3):
    ck('actual_Qsheet_character_'+str(i),J[i].subs(h,-h)+J[i])
# On the ACTUAL double cover h=0 is a ramification chart, not a pole.
# Expressing dh makes the removable 1/h coefficients disappear completely.
Jh=[-2*V*h*a**4*R**2/(3*S3*Delta),
    V*h*a**3*(1-R**3)/(3*Delta),
    a**4*h*(1-R**3)/(9*Delta),
    -V*a**4*(1-R**3)/(9*Delta)]
for i in range(3):
    pck('actual_ramification_chart_is_regular_'+str(i),
        Jh[i]+Jh[3]*s.diff(hf,coords[i])/(2*h)-J[i])

# dy is the ACTUAL spectator, y^2=R/(4D), qc^2=4+y^2.  Thus B(V)=V/(2R)
# and all dqc coefficient legs vanish only after the actual dy wedge.
qlog = 1/(2*R)-2*R**2/S3
Jfixed = [s.cancel(J[0]+V*J[2]/(2*R)),J[1]]
ck('fixed_y_current_dR_coefficient',Jfixed[0]+2*V*h*a**4*R**2/(3*S3*Delta))
ck('full_spectator_connection_restricts_to_dloglambda_n',lg[0]+V*lg[2]/(2*R)-qlog)
fixedcost=s.cancel(qlog*J[1])
ck('full_acceleration_cost_Ra',fixedcost
   +2*V*(1-3*R**3)*(1-R**3)*a**3/(3*S3*h*Delta))

# Exact comparison of the WHOLE cost with I1, not just its common factor.
rr,SS,KK,II=s.symbols('r S K I1', nonzero=True)
I1=V*a**3*(3*R**3-1)/(4*rr*SS**4*KK)
cost_via_I=8*rr*SS*KK*(1-R**3)*I1/(3*h*Delta)
nc=s.cancel(cost_via_I-fixedcost).as_numer_denom()[0]
assert s.rem(nc,SS**3-S3,SS)==0
checks['FULL_cost_coefficient_in_I1_physical_Ra_coframe']=True
ck('FULL_cost_coefficient_in_I1_canonical_coframe',
   (8*rr*SS*KK*(1-R**3)/(3*h*Delta))*(SS*rr/KK)
     -8*rr*rr*SS*SS*(1-R**3)/(3*h*Delta))

# Source units from the maintained actual density, not an unweighted CM model.
yy,ff,lamn,Jcan=s.symbols('y f0 lambda_n Jcan', nonzero=True)
ck('source_mass_pJcan',
   (rr/(3*SS**2))*(1/(72*yy**2*KK))*(KK/(SS*rr))
    -1/(216*yy**2*SS**3))
cc,bb,aa,YY=s.symbols('qc b a0 YQ', nonzero=True)
# lambdaQ/lambda_n=3 etaA/(4b) as an ABSOLUTE one-form in a0,qc.
eta_a=2*bb**4*aa**3/YY
eta_c=s.Rational(2,3)*bb*aa**4/YY
ck('absolute_source_Q_SW_factor_dqc',3*eta_c/(4*bb)-aa**4/(2*YY))
fac=s.cancel(3*eta_a/(4*bb)-3*cc*aa**3/(2*YY))
assert s.rem(s.cancel(fac).as_numer_denom()[0],bb**3-cc,bb)==0
checks['absolute_source_Q_SW_factor_da']=True

out={
 'status':'EXACT_ACTUAL_ZERO_MARK_WEIGHTED_CM_CURRENT_WITH_ALL_COSTS; FULL_HEAT_SOURCE_OPEN',
 'checks':checks,'check_count':len(checks),
 'actual_spectator':'y²=R/(4D),qc=V/r,qc²=4+y²,r²=R,S³=R³+1. PhysicalB=partialR+(D/R)partialD+(V/(2R))partialV.',
 'actual_R_map':'XR=S²/R,YR=(1−R³)/r³,YR²=XR³−4,omegaR=dXR/YR=−dR/(Sr).',
 'actual_A_map':'b³=qc,XA=b²a²,YA=YQ=hQ/r,YA²=XA³−4,hQ²=V²a6−4R. etaA=XA*dXA/YA is absolute and includesdqc.',
 'exact_cyclic_projector':'K=2[XA²*YA*omegaR−XR*XA*YR*omegaA]/(XR³−XA³); dK=omegaR*etaA. This equals (2/3)sum_j zeta^j chi(P,zeta^j Q) and carries exact finite characters, without a closed-form ambiguity.',
 'actual_source_normalization':'f0*dell*dmu=−omegaR*da/(72y²),p=lambda_n*f0,lambda_n=r/(3S²). lambdaQ/lambda_n=3etaA/(4b), includingthefull dqc leg. Thus the fixedy zero-section SW trace has measure −omegaR*etaA/(96y²*b). This evaluates a source-forced section; it is NOT automaticallythewhole3Aheat source.',
 'unweighted_trace_current':'Jtrace=dy*K/(96y²*b) has exterior derivative equal to that full source-normalized zero-section trace, with the actualdy orientation. Coefficient derivatives vanish only afterdy is wedged. Jtrace has nontrivialSdeckcharacter; it is not asserted to descend.',
 'source_character_normalized_current':'Jphys=(lambda_n/b)*K is EXACTLY rational inR,V,a,hQ; Delta=(R³+1)²−R²V²a6. Allr,S,b rootscancelinthisoneform.',
 'rational_current_RaV':[str(s.factor(z))for z in J],
 'FULL_absolute_derivative':'dJphys=lambda_n*omegaR*etaA/b + dlog(lambda_n/b)*Jphys. dlog(lambda_n/b)=[2/(3R)−2R²/(R³+1)]dR−dV/(3V). No coefficient or spectator cost is dropped.',
 'FULL_absolute_source_twoform_Ra_RV_aV':[str(s.factor(z))for z in T],
 'FULL_absolute_cost_twoform_Ra_RV_aV':[str(s.factor(z))for z in cost],
 'fixed_y_current_Ra':[str(s.factor(z))for z in Jfixed],
 'fixed_y_acceleration_cost':str(s.factor(fixedcost)),
 'actual_I1_comparison':'I1=V*a³(3R³−1)/(4rS4K),Dot(lambda_n)=(3R³−1)/(6S4). FULLcost=8rSK(1−R³)*I1*dR*da/(3hQ*Delta)=8RS²(1−R³)*I1*dell*dmu/(3hQ*Delta). The source alpha acceleration is p*I1*dell; the full remaining unit is retained rather than inferred to cancel.',
 'finite_trace':'Jphys is odd underhQ→−hQ. Its ordinarytrace overthezero-markdoublecoveriszero. A source-servinggenus2two-pointkernelmustretainthenecessaryQ-oddcharacterbeforefinitepush. No arbitrary character weight is inserted.',
 'actual_ramification_regular_form_RaVh':[str(s.factor(z))for z in Jh],
 'global_poles':'The apparenthQ=0 pole is REMOVABLE ontheactualdoublecover, as the displayedR,a,V,h current proves. At fixedy thecurrentisregularatr=0andr=infinity. It has possiblepolesalongR³+1=0,Delta=0,andat a=infinity; thea=infinity dr coefficienthasasimplepole, asrequiredbythesecondkindAchannel. No infinitychargeisdiscarded. These needproperrelativecurrenttreatment; no unsupportedGysinclaim ismade.',
 'proper_zero_mark_labels':'FreshglobalactualD0labels:T=r*sigma³,hQ=−T+R/T,a³=(T+R/T)/V. ThusYQ=−(sigma³−sigma^-3),g(Q)=−(sigma³+sigma^-3). YQdeckisT↔R/T (sigma↔sigma^-1 upcube rotations). Also retainthesectioncubiccoverAphys*k³+k²/2=V; D0pointisthelineprojectiontwinoftheoldx0pointthrough(k,0). Ordinaryfinitepushmustcarrybothlabels.',
 'whole_source_guard':'No coefficient multiplying this CM current has been derived fromtheentire3Aheat*lambdaSW genus2 source. Fullrank4agentowns that markedkernel. This artifact suppliesanexactsource-normalizedcurrent,itslegalfinitecharacter,andthecompleteaccelerationcosttobecomparedthere.',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual weighted CM current/source units, absolute costs and finite characters')
