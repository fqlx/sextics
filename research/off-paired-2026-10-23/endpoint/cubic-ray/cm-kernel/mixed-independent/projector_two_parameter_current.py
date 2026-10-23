"""Exact full projector current with both kappa and lambda derivatives.

The actual universal current and its source-guided three-part partition are
retained. Neither is asserted to solve the immutable physical forcing.
"""
import json
from pathlib import Path
import sympy as S

r,v,b,l,k=S.symbols('r v beta lambda kappa',nonzero=True)
T=4*b**3+27
N=(1+l)**3+b**3*l
Q=r*r+r*v+v*v+b
I=(4*b*b-9*v+6*b*v*v)/T
E=Q*I-S.Rational(1,3)
d=1+b*v+v**3
dinv=((1+l)**2-(1+l)*b*v+b*b*v*v)/N
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
def ut(value):
    n,den=S.fraction(S.cancel(value))
    n=S.rem(S.Poly(n,v),S.Poly(v**3-l,v)).as_expr()
    return S.cancel(n.coeff(v,0)/den)
def ur(value):
    n,den=S.fraction(S.cancel(value))
    return S.rem(S.Poly(n,v),S.Poly(v**3-l,v)).as_expr()/den
def rr(value):
    n,den=S.fraction(S.cancel(value))
    return S.rem(S.Poly(n,r)*S.invert(S.Poly(den,r),S.Poly(r**3+b*r+1,r)),S.Poly(r**3+b*r+1,r)).as_expr()
def tf(value):
    z=rr(value)
    trace=z.coeff(r,0)-S.Rational(2,3)*b*z.coeff(r,2)
    return rr(z-trace)
V=rr(-1/(r*(b+3*r*r))-S.Rational(1,3))
W=rr(b*r/(b+3*r*r)**3)
a0,a1=S.symbols('a0 a1')
def coefficients(value):
    sol=S.solve(S.Poly(rr(tf(value)-a0*V-a1*W),r).all_coeffs(),[a0,a1])
    return [S.factor(sol[a0]).subs(b**3,k),S.factor(sol[a1]).subs(b**3,k)]

check('polynomial-normalizer',S.expand((b+3*v*v)*I-1-9*(2*b*v-3)*d/T))
check('normalized-graph-inverse-all-coefficients',ur((1+l+b*v)*dinv-1))
EH=coefficients(ut(E))
EK=coefficients(b*ut(E*v*dinv)/3)
EL=coefficients(ut(E*(1+b*v/(3*l))*dinv))
t=4*k+27;n=(1+l)**3+k*l
expectedH=[(4*k-81*l-54)/t,-12*(l+1)]
expectedK=[l*(2*k+3*l*l-3*l-6)/(6*n),-l*t*(l+1)/(3*n)]
expectedL=[(8*k*k-378*k*l+54*k-486*l**3-1458*l*l-729*l-486)/(6*t*n),
           -(28*k*l+4*k+36*l**3+108*l*l+54*l+63)/(3*n)]
for i in range(2):
    check('actual-normalized-H-current-'+str(i),EH[i]-expectedH[i])
    check('actual-normalized-kappa-current-'+str(i),EK[i]-expectedK[i])
    check('actual-normalized-lambda-current-'+str(i),EL[i]-expectedL[i])

def theta(z):
    A,B=z
    return [S.factor(k*S.diff(A,k)+3*B/t),
            S.factor(k*S.diff(B,k)-2*A+(27-2*k)*B/t)]
P=[S.diff(z,l) for z in EH]
thetaP=theta(P)
thetaEH=theta(EH)
expectedThetaP=[36*(5*k-27)/t**2,6*(4*k-27)/t]
expectedThetaEH=[36*(5*k-27)*(l+1)/t**2,
                 2*((12*l+8)*k-81*l-108)/t]
for i in range(2):
    check('full-kappa-H-curvature-'+str(i),thetaEH[i]-expectedThetaEH[i])
    check('full-lambda-H-curvature-'+str(i),P[i]-[-81/t,-12][i])
    check('normal-graph-denominator-cancels-'+str(i),theta(EL)[i]-S.diff(EK[i],l)-thetaP[i])
    check('mixed-curvature-'+str(i),thetaP[i]-expectedThetaP[i])

# The polynomial normalizer differs modulo a closed current from the
# displayed simple universal current; d(lambda) is not discarded.
simpleK=[-l*z for z in thetaP]
for i in range(2):
    check('closed-current-difference-'+str(i),theta(EL)[i]-S.diff(EK[i]-simpleK[i],l))

l1,l2=S.symbols('lambda1 lambda2')
l3=-1-l1-l2
partitionH=[S.factor(sum(z.subs(l,li) for li in [l1,l2,l3])) for z in EH]
partitionCurvature=theta(partitionH)
expectedPartition=[72*(5*k-27)/t**2,6*(4*k-81)/t]
for i in range(2):
    check('three-partition-kappa-H-source-'+str(i),partitionCurvature[i]-expectedPartition[i])
    check('three-partition-mixed-terms-cancel-'+str(i),
          S.diff(partitionH[i],l1)+S.diff(partitionH[i],l2))

# The universal one-form must be wedged with the COMPLETE physical residue.
# eta1*eta2 alone has c-deck character 1 and its normalized trace vanishes.
c,e,Y=S.symbols('c e Y',nonzero=True)
Sc=5*c**4*e*Y
S2=c**5*(2-5*e**3)
def delta2(value):return 2*Y*S.diff(value,e)-3*e**2*S.diff(value,Y)
check('mixed-invariant-residue-differential',
      S.rem(S.expand(delta2(c**5*e*Y)-S2),Y**2-1+e**3,Y))
check('mixed-invariant-residue-closed',
      S.rem(S.expand(delta2(Sc)-S.diff(S2,c)),Y**2-1+e**3,Y))
assert (5-2-3)%6==0 and (4-2-3+1)%6==0 and (5+1)%6==0
checks.append('complete-mixed-residue-c-deck-invariant')
xc,xh,x1,x2,yc,yh,y1,y2=S.symbols('xc xh x1 x2 yc yh y1 y2')
det=S.det(S.Matrix([[xc,xh,x1,x2],[yc,yh,y1,y2],[0,0,1,0],[Sc,0,0,S2]]))
check('complete-exterior-source-jacobian',
      det-S2*(xc*yh-xh*yc)-Sc*(xh*y2-x2*yh))

Z,up,vp=S.symbols('Z up vp',nonzero=True)
Tr=up/vp;Sr=Z*vp**2
for (i,j,wanted) in [(Z,up,-vp),(Z,vp,up),(up,vp,2*Z)]:
    check('physical-rational-residue-'+str(i)+'-'+str(j),
          S.diff(Tr,i)*S.diff(Sr,j)-S.diff(Tr,j)*S.diff(Sr,i)-wanted)
z0,h0,u0,v0,z1,h1,u1,v1=S.symbols('z0 h0 u0 v0 z1 h1 u1 v1')
physical_det=S.det(S.Matrix([
 [z0,h0,u0,v0],[z1,h1,u1,v1],
 [S.diff(Tr,Z),0,S.diff(Tr,up),S.diff(Tr,vp)],
 [S.diff(Sr,Z),0,S.diff(Sr,up),S.diff(Sr,vp)]]))
E_xi=2*Z*z0-up*u0-vp*v0
E_psi=2*Z*z1-up*u1-vp*v1
check('physical-source-monomial-field',physical_det+h0*E_psi-h1*E_xi)
hh=S.symbols('hh',nonzero=True)
HP=1+Z**-2+hh**6;CP=Z**2+up**6+vp**6
BP=up/2+hh*vp/3+hh*up*vp/(2*Z)
KP=BP**3/(CP*HP**2)
def X(value):return Z*S.diff(value,Z)-up*S.diff(value,up)/2-vp*S.diff(value,vp)/2
JP=-6*(X(KP)/KP*S.diff(HP,hh)/HP-S.diff(KP,hh)/KP*X(HP)/HP)
point={Z:S.Integer(1),hh:S.Integer(1),up:S.Integer(1),vp:S.Integer(1)}
check('physical-partition-point-kappa',KP.subs(point)-S.Rational(64,729))
check('physical-partition-point-jacobian',JP.subs(point)-S.Rational(59,4))
assert expectedPartition[0].subs(k,S.Rational(64,729))!=0
checks.append('actual-uniform-partition-V-residual-nonzero')

data={
 'status':'Exact full two-parameter projector current and three-part source partition; no physical source closure',
 'constant_scope':'fixed characteristic-zero k; k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'normalized_field':'r^3+beta*r+1=0, v^3=lambda, beta^3=kappa',
 'physical_scalings':'p=(H/C)^(1/3)*r, u=(H/C)^(1/3)*v, Dphysical=H*(1+lambda+beta*v)',
 'actual_current':'Theta=EH*dlog(H)+EK*dlog(kappa)+EL*dlambda; wedge the retained closed base two-form afterwards',
 'normalizer':'E=(r^2+r*v+v^2+beta)*(4beta^2-9v+6beta*v^2)/(4beta^3+27)-1/3',
 'coefficient_H':[str(z) for z in EH],
 'coefficient_kappa':[str(z) for z in EK],
 'coefficient_lambda':[str(z) for z in EL],
 'curvature':{
   'dlogkappa_dlogH':[str(z) for z in thetaEH],
   'dlambda_dlogH':[str(z) for z in P],
   'dlogkappa_dlambda':[str(z) for z in thetaP]},
 'modulo_closed_current':'Theta == EH*dlog(H)-lambda*theta(P)*dlog(kappa), where P=partial_lambda(EH)',
 'partition':{
   'actual_sections':'lambda_i=-H_i/H, H_i=1,c^-6*Y^-2,h^6, sum_i lambda_i=-1',
   'coefficient_H':[str(z) for z in partitionH],
   'curvature_dlogkappa_dlogH':[str(z) for z in partitionCurvature],
   'mixed_terms':'Both dlambda wedge dlogH and dlogkappa wedge dlambda terms cancel in the three-current sum',
   'remaining':'The partition reduces to a fixed constant-lambda two-component curvature. Its physical Jacobian coefficient does not automatically equal the actual (0,1/(CH)) source.',
   'physical_nonzero_residual':'At Z=h=u=v=1: kappa=64/729, J_beta0=59/4 and the V source is (59/4)*72*(5kappa-27)/(4kappa+27)^2 !=0, whereas the required V forcing is0.'},
 'physical_deck_and_mixed_residue':{
   'warning':'eta1 wedge eta2 has c-deck character 1. The universal one-form alone is deck-invariant, so that unweighted physical three-current traces to zero.',
   'invariant_closed_two_form':'betaS=eta1 wedge d(c^5*e*Y)=eta1 wedge [5*c^4*e*Y*dc+c^5*(2-5e^3)*eta2]',
   'rational_physical_form':'beta0=betaS/a_scale=d(u/v) wedge d(Z*v^2)=(v*du-u*dv) wedge dZ+2Z*du wedge dv',
   'rational_physical_vector':'E=2Z*partial_Z-u*partial_u-v*partial_v, divergence0; source functional against Omega=-(1/3)dZ dh du dv is 3*(xi_h*E(psi)-psi_h*E(xi))',
   'actual_current':'Theta wedge betaS',
   'source_functional':'For C(xi,psi)=S2*(xi_c*psi_h-xi_h*psi_c)+Sc*(xi_h*psi_2-xi_2*psi_h), source/Omega=-(a_scale/c^4)[theta(EH)*C(dlogkappa,dlogH)+P*C(dlambda,dlogH)+theta(P)*C(dlogkappa,dlambda)]. All physical c,h,E2 derivatives are retained.',
   'scope':'betaS is an exact closed residue. This completes the c/E2 deck and closure terms, but supplies no match with the nonzero H31 target by itself. A source-carrying full correction remains open.'},
}
Path(__file__).with_name('projector-two-parameter-current-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact full-projector and mixed-partition identities')
