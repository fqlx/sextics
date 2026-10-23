#!/usr/bin/env python3
"""Bind the actual infinity gauge after polynomial-moment properization."""
import hashlib,json
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent
i,u,w=s.symbols('i u w')
proper_path=HERE/'actual-polynomial-moment-preimages.json'
proper=json.loads(proper_path.read_text())
uK=s.QQ.frac_field(u)
P=lambda f:s.Poly(f,w,domain=uK)
N=P(9*w*w-16*u*(1+w**3))
load=lambda ar:sum(s.sympify(c,locals={'u':u})*w**j for j,c in enumerate(ar))
qhh,remh=P(54*w*(1+w**3)/u).div(N)
F0=s.cancel(P(load(proper['properized_potentials']['remF_coefficients'])).nth(2)/(128*u))
G0=s.cancel(P(load(proper['properized_potentials']['remG_coefficients'])).nth(2)/(128*u))
H0=s.cancel(P(load(proper['properized_potentials']['remH_coefficients'])).nth(2)/(128*u))
h0=s.cancel(remh.nth(2)/(128*u))
th=lambda f:u*s.diff(f,u)
c1=s.factor(20*(h0-F0)+16*th(h0-F0)-2*(G0+th(G0))
             -24*th(th(H0))+24*th(H0)-4*H0)
c2=s.factor(4*th(F0)-3*F0+8*s.diff(G0,u)-2*G0/u)

# Check the limiting Cartan rows with an unrestricted coefficient q(i,J).
j=s.symbols('J')
q=s.Function('q')(i,j)
v=j/(36*i**2*w**8)
A=lambda f:s.diff(f,i)-w/(4*i)*s.diff(f,w)
B=lambda f:s.diff(f,j)+w/(8*j)*s.diff(f,w)
Z=lambda f:-w*s.diff(f,w)/8
D=lambda f:6*Z(f)-2*i*A(f)-2*j*B(f)
E=lambda f:i*s.diff(f,i)+j*s.diff(f,j)
Db=lambda f:6*f-2*E(f)
EA=lambda f:2*f/(i*v)
EB=lambda f:-f/(j*v)
EZ=lambda f:f/v
ED=lambda f:4*f/v
EL=lambda f:3*f/v
EM=lambda f:s.Integer(0)
ES=lambda f:Db(ED(f))-6*ED(f)+ED(D(f)-5*f)
EPE=lambda f:ES(f)+s.diff(EL(f),i)+EA(Z(f)+D(f)/2-2*f)
EPD=lambda f:4*j*(s.diff(EB(f),j)+EB(B(f)))+2*EB(f)+EA(Z(f)+j*B(f))
EA3=lambda f:s.diff(EA(f),i,2)+s.diff(EA(A(f)),i)+EA(A(A(f)))
rows={
 'ES':(ES(v*q),4*q-16*E(q)),
 'EPE':(EPE(v*q),4*q-16*E(q)+3*s.diff(q,i)+2*(2*q-E(q))/i),
 'EPD':(EPD(v*q),-8*s.diff(q,j)+2*q/j+2*(q+j*s.diff(q,j))/i),
 'EA3':(EA3(v*q),6*s.diff(q,i,2)/i-6*s.diff(q,i)/i**2+4*q/i**3),
}
checks=[]
for label,(a,b) in rows.items():
    assert s.expand(a-b)==0,label
    checks.append('unrestricted limiting Cartan row '+label)

# The chosen polynomial primitives have zero constant coefficient; every
# proper term in the independently checked Hermite primitive tends to zero.
# Therefore its polynomial infinity constant remains exactly zero after
# adding the parameter-only barred operators applied to QF,QG,QH.
pn=json.loads((HERE.parent/'ruling-source/adjoint-reconstruction/n-only-hermite-results.json').read_text())
assert pn['source_sha256']==proper['source_sha256']
for part in pn['components'].values():
    assert s.sympify(part['polynomial_primitive_coefficients'][0])==0
    for term in part['proper_primitive_terms']:
        assert len(term['numerator_coefficients'])-1<3*term['denominator_power']
for preimage in proper['moment_preimages'].values():
    assert s.sympify(preimage['coefficients'][0])==0
checks.append('actual N-only primitive and properization have zero polynomial constant')

inf_path=HERE.parent/'ruling-source/adjoint-reconstruction/source-infinity-preimage-results.json'
inf=json.loads(inf_path.read_text())
assert inf['source_sha256']==proper['source_sha256']
assert inf['checks']>=7
checks.append('preferred actual infinity preimage source bound')
out={
 'source_sha256':proper['source_sha256'],
 'properization_file_sha256':hashlib.sha256(proper_path.read_bytes()).hexdigest(),
 'infinity_preimage_file_sha256':hashlib.sha256(inf_path.read_bytes()).hexdigest(),
 'properized_moment_limits':{'hproper_over_v':str(h0)+' * i^-1',
   'Fproper_over_v':str(s.factor(F0))+' * i^-1',
   'Gproper_over_v':str(s.factor(G0)),
   'Hproper_over_v':str(s.factor(H0))+' * i^2'},
 'Jproper_constant_at_infinity':{'i^-1':str(c1),'i^-2':str(c2)},
 'Jproper_definition':'K/v+LEQF+LDQG+L3(QH_minus+QH_plus)',
 'preferred_QDinf':inf['preferred_QDinf'],
 'actual_normal_form':'Jnorm=Jproper-LD(QDinf)-i^-1*c1(u)-i^-2*c2(u)',
 'actual_potentials':{'F':'Fproper','G':'Gproper+v*Z(QDinf)','H':'Hproper'},
 'actual_source_identity':'Ssrc-PE(Fnew)-PD(Gnew)-P3(Hnew)=(Z-1)[v*Jnorm]',
 'infinity_behavior':'Jnorm=O(w^-1); every positive and constant infinity coefficient has been served explicitly',
 'constant_reason':'N-only proper primitive has zero infinity constant. Source polynomial moment yields D(D+1)Ph, which has w2,w1 but no constant. The remaining Cartan constants are the four checked parameter rows.',
 'fold_bound':5,
 'fold_reason':'Full cubic properization may create order5 in K/v; the preferred quadratic LD lift and parameter-only gauge do not raise it.',
 'checks':checks,'passed':len(checks),'certificate':False,
 'scope':'Actual source-bound scalar normal form; all compact and infinity curve defects remain to be served',
}
path=HERE/'properized-infinity-gauge.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
 'c1_size':len(str(c1)),'c2_size':len(str(c2)),'infinity_order':-1,'fold_bound':5},indent=2))
