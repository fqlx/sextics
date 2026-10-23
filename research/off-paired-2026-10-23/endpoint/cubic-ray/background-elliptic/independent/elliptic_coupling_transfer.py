"""Exact source-guided H/q transfer through the background elliptic factors.

The endpoint C coupling is differentiated literally.  Its invariant residual
lives on the background genus-two quotient; no primitive or correspondence
between the two genus-two Jacobians is asserted.
"""
import json
from pathlib import Path
import sympy as S

q,z,K,s,d=S.symbols('q z K0 s d',nonzero=True)
fp=2*q**3-z*q/2-K
fm=-2*q**3-z*q/2-K
GB=S.groebner([s*s-fp,d*d-fm],s,d,domain=S.QQ.frac_field(q,z,K))
checks=[]
def rem(value):
    n,den=S.fraction(S.cancel(value))
    return S.cancel(GB.reduce(n)[1]/den)
def check(name,value):
    r=rem(value)
    assert r==0,(name,S.factor(r))
    checks.append(name)

mu=1/d-1/s;nu=1/d+1/s
C=q/3+z*(s+d)/4
CH=z*nu/8
lp=3*q*q-z/4;lm=-3*q*q-z/4
Cq=S.Rational(1,3)+z*(lp/s+lm/d)/4
Cz=(s+d)/4-z*(q/4+3*z**5)*nu/4
w=s*d
check('literal-C-H',CH-S.diff(C,s)/(2*s)-S.diff(C,d)/(2*d))
check('literal-C-q',Cq-S.diff(C,q)-S.diff(C,s)*lp/s-S.diff(C,d)*lm/d)
check('literal-C-z',Cz-S.diff(C,z)+(q/4+3*z**5)*(S.diff(C,s)/s+S.diff(C,d)/d))
check('source-times-C-H-descends',mu*CH-z*q**3/(2*w**2))
check('source-times-C-z-descends',mu*Cz-q**3/w+z*q**3*(q/4+3*z**5)/w**2)
check('source-times-affine-C-descends',mu*(C-q/3)-z*q**3/w)

def elliptic_data(a):
    Delta=27*a*K*K-z**3/2
    AA=9*a*K/(2*Delta)
    BB=3*a*z/(2*Delta)
    RR=(z*z+9*a*K*q-3*a*z*q*q)/Delta
    f=a*q**3-z*q/2-K
    # dH(f)=+1 because K0=1+z6-H.
    identity=(AA+BB*q+S.diff(RR,q))*f-RR*S.diff(f,q)/2+S.Rational(1,2)
    check('literal-elliptic-H-reduction-'+str(a),identity)
    return AA,BB,RR
Ap,Bp,Rp=elliptic_data(S.Integer(2))
Am,Bm,Rm=elliptic_data(S.Integer(-2))
T=Rm/d-Rp/s
G=(Am+Bm*q)/d-(Ap+Bp*q)/s
muH=-1/(2*d**3)+1/(2*s**3)
def Dq(value):return S.diff(value,q)+lp/s*S.diff(value,s)+lm/d*S.diff(value,d)
check('full-background-H-source-reduction',muH-Dq(T)-G)

Qinv=z*q**3/(2*w*w)-z*S.Rational(1,4)*(
       (Rm*lp-Rp*lm)/w+Rm*lm/fm-Rp*lp/fp)
check('actual-coupling-residual-splits',mu*CH-T*Cq+T/3-Qinv)
check('third-genus-two-quotient',w*w-(K+z*q/2)**2+4*q**6)
check('simultaneous-sign-T-anti',T.subs({s:-s,d:-d},simultaneous=True)+T)
check('simultaneous-sign-G-anti',G.subs({s:-s,d:-d},simultaneous=True)+G)
check('simultaneous-sign-invariant-residual',Qinv.subs({s:-s,d:-d},simultaneous=True)-Qinv)

# Endpoint row bookkeeping for the actual H/q three-current.  Denote the
# formal columns by e=omega0, hcol=nabla_H|C e, ccol=nabla_C e.
e,hcol,ccol=S.symbols('e hcol ccol')
source=-mu*hcol/72
divJH=-(mu*(hcol+CH*ccol)+muH*e)/72
divJq=(Dq(T)*e+T*Cq*ccol)/72
residual=(G*e+(mu*CH-T*Cq)*ccol)/72
for formal_column in [e,hcol,ccol]:
    check('source-carrying-two-direction-current-'+str(formal_column),
          S.expand(source-divJH-divJq-residual).coeff(formal_column))

data={
 'status':'Actual source-guided H/q current with retained elliptic and third-genus-two correction; no primitive or Picard claim',
 'constant_scope':'fixed characteristic-zero k; k=C for full certificate contract',
 'check_count':len(checks),'checks':checks,
 'physical_source':'-(mu/72)*nabla_H|C(omega0) dH wedge dq wedge dz, mu=1/d-1/s',
 'C':'q/3+z*(s+d)/4',
 'C_H':str(CH),'C_q':str(Cq),'C_z':str(Cz),
 'elliptic_data':{
   'plus':{'A':str(Ap),'B':str(Bp),'R':str(Rp)},
   'minus':{'A':str(Am),'B':str(Bm),'R':str(Rm)}},
 'T':str(T),'G':str(G),
 'cohomological_current':'J=-mu*omega0 dq wedge dz/72-T*omega0 dH wedge dz/72; literal endpoint Dwork primitives must also be transported',
 'source_identity':'source=dJ+[G*omega0+(mu*C_H-T*C_q)*nabla_C(omega0)] dH wedge dq wedge dz/72',
 'coupling_residual':'mu*C_H-T*C_q=-T/3+Q_invariant(q,w)',
 'Q_invariant':str(Qinv).replace('d*s','w'),
 'background_quotient':'w^2=(K0+z*q/2)^2-4q^6, w=s*d; same endpoint-type family at parameters (K0,z/2)',
 'parameter_transport':'For its universal connection, physical D_H=-nabla_K0 and D_z=6z^5*nabla_K0+nabla_(z/2)/2; q held fixed',
 'gap':'The invariant correction and anti-character G,T corrections are nonzero and retain endpoint C=q/3+z(s+d)/4. Splitting the background differential is not an endpoint Jacobian splitting or a source primitive.',
}
Path(__file__).with_name('elliptic-coupling-transfer-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact elliptic-source and physical-coupling identities')
