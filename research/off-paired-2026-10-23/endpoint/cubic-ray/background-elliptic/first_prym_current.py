"""Literal source-first Prym current and off-diagonal translations.

The source is the immutable endpoint derivative coupled to the full physical
background. All physical C derivatives and elliptic exact terms are retained.
No closure or primitive is asserted.
"""
import json
from pathlib import Path
import sympy as S

q,z,H,p,s,d,Z=S.symbols('q z H p s d Z',nonzero=True)
wH,wC,w0=S.symbols('wH wC w0')
K=1+z**6-H
Fp=2*q**3-z*q/2-K
Fm=-2*q**3-z*q/2-K
G=S.groebner([s*s-Fp,d*d-Fm],s,d,domain=S.QQ.frac_field(q,z,H,p,Z,wH,wC,w0))
checks=[]
def reduce(value):
    n,den=S.fraction(S.cancel(value))
    return S.cancel(G.reduce(n)[1]/den)
def check(name,value):
    result=reduce(value)
    assert result==0,(name,S.factor(result))
    checks.append(name)
def dh(f):return S.diff(f,H)+S.diff(f,s)/(2*s)+S.diff(f,d)/(2*d)
def dq(f):return S.diff(f,q)+(3*q*q-z/4)*S.diff(f,s)/s+(-3*q*q-z/4)*S.diff(f,d)/d
C=q/3+z*(s+d)/4
CH=z*(1/s+1/d)/8
Cq=S.Rational(1,3)+z*((3*q*q-z/4)/s+(-3*q*q-z/4)/d)/4
theta=(1/d-1/s)/12
thetaH=(1/s**3-1/d**3)/24
check('physical-C-H',dh(C)-CH)
check('physical-C-q',dq(C)-Cq)
check('actual-Prym-source-H-derivative',dh(theta)-thetaH)
check('physical-C-H-source-rationalizes',CH*theta-z*q**3/(24*s*s*d*d))

# omega0=dp/Z, literal fixed-C H derivative=-S/Z^3 and C derivative=-Sp/Z^3.
# In coordinates H,q,z, its physical H derivative is omega_H+CH*omega_C.
omegaH=wH
omegaC=wC
omega0=w0
source=-omegaH*theta/6
dJ0=-(omegaH*theta+CH*omegaC*theta+omega0*thetaH)/6
remainder=z*q**3*omegaC/(144*s*s*d*d)+(1/s**3-1/d**3)*omega0/144
check('literal-source-first-current',source-dJ0-remainder)

# Reduce theta_H with the exact elliptic GM columns, while retaining the
# resulting endpoint C_q term from integration by parts in q.
D=H-1-z**6
B=-z/2
def RD(A):return (6*A*B*q*q-9*A*D*q+4*B*B)/(27*A*D*D+4*B**3)
def MD0(A):return -9*A*D/(2*(27*A*D*D+4*B**3))
def MD1(A):return -3*A*B/(27*A*D*D+4*B**3)
Rp,Rm=RD(2),RD(-2)
tau=(Rm/d-Rp/s)/12
thetaHcohom=((MD0(-2)+MD1(-2)*q)/d-(MD0(2)+MD1(2)*q)/s)/12
for A in [2,-2]:
    fa=A*q**3+B*q+D
    ident=-S.Rational(1,2)-(MD0(A)+MD1(A)*q)*fa-S.diff(RD(A),q)*fa+RD(A)*S.diff(fa,q)/2
    assert S.cancel(ident)==0
    checks.append('elliptic-GM-exact-first-column-A='+str(A))
coefficientC=CH*theta-tau*Cq
mixedThird=S.factor(z*(Rm*(3*q*q-z/4)-Rp*(-3*q*q-z/4))/48)
assert mixedThird!=0
checks.append('background-third-quotient-term-is-retained')

# Verify the actual q-current sign independently at the coefficient level:
# d[tau omega0^dH^dz]/(omega-first top frame)=tau_q omega0+tau*Cq omegaC.
thetaHformal,tauqformal,thetaCformal=S.symbols('thetaHformal tauqformal thetaCformal')
afterGMformal=((CH*theta-tau*Cq)*omegaC+thetaCformal*omega0)/6
dJtauformal=(tauqformal*omega0+tau*Cq*omegaC)/6
remainderformal=(CH*theta*omegaC+thetaHformal*omega0)/6
assert S.cancel((remainderformal-dJtauformal-afterGMformal).subs(thetaHformal,thetaCformal+tauqformal))==0
checks.append('full-elliptic-GM-current-retains-C-q')

# Independent off-diagonal product coordinates.
Q,delta,a,b=S.symbols('Q delta a b')
rels=[a*a+b*b-3*Q*Q*delta-delta**3/4+z*Q/2+K,
      a*b-Q**3-3*Q*delta**2/4+z*delta/8]
coords=[Q,delta,a,b]
Wc=[a,2*b,3*Q*delta-z/4,3*Q*Q+3*delta*delta/4]
Vc=[b,2*a,3*Q*Q+3*delta*delta/4,3*Q*delta-z/4]
def W(f):return sum(v*S.diff(f,t) for t,v in zip(coords,Wc))
def V(f):return sum(v*S.diff(f,t) for t,v in zip(coords,Vc))
for i,r in enumerate(rels):
    assert S.expand(W(r))==0 and S.expand(V(r))==0
    checks.append('off-diagonal-relations-'+str(i))
for i,t in enumerate(coords):
    assert S.expand(W(V(t))-V(W(t)))==0
    checks.append('commuting-product-translations-'+str(i))
Cext=Q/3+z*a/2
WC=a/3+3*z*Q*delta/2-z*z/8
VC=b/3+3*z*Q*Q/2+3*z*delta*delta/8
assert S.expand(W(Cext)-WC)==0 and S.expand(V(Cext)-VC)==0
checks.append('full-off-diagonal-C-corrections')
assert S.expand(W(WC).subs(delta,0)-(-z/12+3*z*Q*b))==0
assert S.expand(W(WC).subs(delta,0)-W(a/3-z*z/8).subs(delta,0)-3*z*Q*b)==0
checks.append('restriction-before-second-translation-loses-term')

data={
 'status':'Actual first Prym source current and exact full remainder; no primitive',
 'constant_scope':'fixed characteristic-zero k; k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'background':{'s2':str(Fp),'d2':str(Fm),'C':str(C)},
 'source':'S=-omegaH|C ^ dH ^ theta ^ dz/6, theta=(dq/d-dq/s)/12',
 'actual_first_current':'J0=+omega0^theta^dz/6; fiber-first orientation',
 'literal_remainder':'S-dJ0=[z*q^3*omegaC/(144*s^2*d^2)+(1/s^3-1/d^3)*omega0/144]^dH^dq^dz',
 'elliptic_GM_reduction':{
    'tau':str(tau),'thetaH_cohom_dq_coefficient':str(thetaHcohom),
    'additional_current':'Jtau=tau*omega0^dH^dz/6',
    'full_remaining':'S-d(J0+Jtau)=[(C_H*theta-tau*C_q)*omegaC+thetaHcohom*omega0]^dH^dq^dz/6',
    'mixed_third_quotient':'The -tau*C_q coefficient includes -[mixedThird/(s*d)], with mixedThird='+str(mixedThird),
    'warning':'Multiplying an elliptic exact derivative by the endpoint kernel creates the retained C_q*omegaC term.'},
 'product_translation':{'coordinates':'Q=(qplus+qminus)/2, delta=qplus-qminus,a=(s+d)/2,b=(s-d)/2',
    'W':{str(t):str(v) for t,v in zip(coords,Wc)},
    'Wprime':{str(t):str(v) for t,v in zip(coords,Vc)},
    'Cext':str(Cext),'WC':str(WC),'WprimeC':str(VC),
    'normal_velocity':'W(delta)|delta=0=2b=2y^3; Wprime(delta)|delta=0=2a=2x^3',
    'second_translation_warning':'[W^2C]|delta=0=-z/12+3zQb, whereas W([WC]|delta=0)|delta=0=-z/12'},
 'gap':'The rational MC forcing, both elliptic first/second-kind terms, and the background genus-two cross term remain to be cancelled with full H,z current derivatives.',
}
Path(__file__).with_name('first-prym-current-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact actual-current, elliptic-correction and off-diagonal-translation checks')
