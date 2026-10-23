"""Full product trace of SOURCE Y-seed CM repair; derivatives are not dropped."""
from pathlib import Path
import sympy as s,json
H,t,rho,y=s.symbols('H t rho y',nonzero=True)
D=H-2*t**3;d=t/(4*rho);K=1+d*d-H
de=-(t**3+1)/(4*rho*rho)
cl=lambda e:s.factor(s.cancel(e))
def red(e):
 n,den=s.together(e).as_numer_denom()
 n=s.rem(s.Poly(n,y),s.Poly(y*y-H+1,y)).as_expr()
 n=s.rem(s.Poly(n,rho),s.Poly(rho*rho-2*t**3+1,rho)).as_expr()
 return s.factor(n)
# Basis eta,dH,psi=dlogPsi; h-normalized trace of h²yKP.
Om=[2*t*H*y*(y+rho)/D,-2*t*t*(y+rho)/(3*D),s.S(0)]
aux=[-2*y*de/K,d/(y*K),s.S(0)]
logb=[aux[0]/2,aux[1]/2,s.Rational(1,2)]
wedge=lambda a,b:[cl(a[0]*b[1]-a[1]*b[0]),cl(a[0]*b[2]-a[2]*b[0]),cl(a[1]*b[2]-a[2]*b[1])]
actual=wedge(Om,logb)
avg=[cl((a+a.subs(y,-y))/2)for a in actual]
E=t*t*(H*(8*t**3-1)-2*(t**3+1))/(12*D*K*rho*rho)
expected=[E,t*H*(H-1)/D,-t*t*rho/(3*D)]
checks={'WHOLE_ytrace_including_spinor_and_PQ_legs':all(red(a-b)==0 for a,b in zip(avg,expected))}
# rho deck holds actual x,y,z (hence physical H,U,W,t) fixed: eta andpsi odd.
parity=[-1,1,-1] # eta∧dH, eta∧psi, dH∧psi.
last=[cl((a+sgn*a.subs(rho,-rho))/2)for a,sgn in zip(expected,parity)]
checks['WHOLE_original_rho_trace_including_form_parity']=all(cl(a-b)==0 for a,b in zip(last,[0,t*H*(H-1)/D,-t*t*rho/(3*D)]))
assert all(checks.values()),checks
out={
 'status':'FULL_SOURCE_Y_CM_REPAIR_TRACE_NOT_FULL_CERTIFICATE',
 'checks':checks,'check_count':len(checks),
 'scope':'The h-trace formula is independently supplied by parent/algebraic audit; this script checks the WHOLE subsequent y and rho traces including moving dlogb. It never multiplies independent traces.',
 'h_trace':'Tr_h(h²*y*KP)=2(y+rho)/(H−2t³)*[t*y*H*eta−t²*dH/3]',
 'physical_spinor':'dlogb=(dlogPsi+dlogPsi_aux)/2; dlogPsi_aux=d*dH/(yK)−2y*Deta(d)*eta/K, d=t/(4rho),Deta(d)=−(t³+1)/(4rho²),K=H0−H.',
 'FULL_h_y_trace':'[tH(H−1)eta−t²rho*dH/3]/(H−2t³) wedge dlogPsi + E*eta wedge dH',
 'E':str(E),
 'actual_rho_deck':'rho→−rho at fixed original x,y,z gives R,r,d→their negatives, eta→−eta, Psi→Psi^-1, H,U,W,t unchanged. Hence the E*eta*dH term is odd; the entire first two-form is even.',
 'Y_seed_amplitude':'B*Ppoly/(72t*A²),B=U/W−1,A=3(U²−1)−3(2t³+3)z6−tz3,Ppoly=−12U²−6+(24t³−72)z6−tz3. This factor is rho-even in actual original variables.',
 'FULL_descended_CM_current':'J_CMdesc=B*Ppoly/[72t*A²*(H−2t³)] * [tH(H−1)eta−t²rho*dH/3] wedge dlogPsi wedge theta0',
 'rationality':'No alpha,zeta,h,y auxiliary CM radical remains. eta wedge dlogPsi and rho*dlogPsi are rational in the original coefficient field because r=rho*z³−t/(4rho),R=rho*z³,rho²=2t³−1.',
 'mandatory_remaining':'Differentiate the ENTIRE descended current, including amplitude, H,t,actual Psi,endpoint C/H,p,Z and every pole. This is the same source-bound candidate by normalized trace; no residual cancellation is asserted.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'whole CM-repair product trace identities; actual residual still required')
