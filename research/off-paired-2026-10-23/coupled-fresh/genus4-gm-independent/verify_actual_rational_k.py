#!/usr/bin/env python3
"""Audit literal Cartan restoration for the actual source-bound rational K.

This checks the general differential identities and the fixed Hermite matrix.
The independent QQ(u)[w] primitive/source identities are recorded by the
parent's construct_n_only_hermite.py, whose exact output is bound below.
Neither check claims that the retained curve-valued defect has been served.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent
i,J,w,beta=s.symbols('i J w beta')
checks=[]
def zero(x,name):
    assert s.cancel(x)==0,name
    checks.append(name)

# Generic one-step Cartan identities: v and Q are unrestricted functions.
vg=s.Function('v')(i,J,w)
Qg=s.Function('Q')(i,J,w)
mg=s.diff(vg,w)/vg**2
for label,var in [('A',i),('B',J)]:
    lhs=mg*(s.diff(Qg,var)-s.diff(vg,var)/s.diff(vg,w)*s.diff(Qg,w))
    rhs=s.diff(mg*Qg,var)+s.diff(-Qg*s.diff(vg,var)/vg**2,w)
    zero(lhs-rhs,'generic Cartan '+label)
zero(mg*vg/s.diff(vg,w)*s.diff(Qg,w)-mg*Qg-s.diff(Qg/vg,w),
     'generic Cartan Z')

# A nonlinear rational test section for the full product corrections.
# Choosing a linear coordinate v keeps this audit independent and compact;
# the preceding unrestricted identities prove the same correction generally.
v=i+J*w
m=s.diff(v,w)/v**2
Q=(i+J*w+w**2)/(1+w)
ca=lambda x:s.cancel(x)
A=lambda x:ca(s.diff(x,i)-s.diff(v,i)/s.diff(v,w)*s.diff(x,w))
B=lambda x:ca(s.diff(x,J)-s.diff(v,J)/s.diff(v,w)*s.diff(x,w))
Z=lambda x:ca(v/s.diff(v,w)*s.diff(x,w))
D=lambda x:ca(6*Z(x)-2*i*A(x)-2*J*B(x))
Db=lambda x:ca(6*x-2*i*s.diff(x,i)-2*J*s.diff(x,J))
EA=lambda x:ca(-x*s.diff(v,i)/v**2)
EB=lambda x:ca(-x*s.diff(v,J)/v**2)
EZ=lambda x:ca(x/v)
ED=lambda x:ca(6*EZ(x)-2*i*EA(x)-2*J*EB(x))
EL=lambda x:ca(EZ(x)+ED(x)/2)
EM=lambda x:ca(EZ(x)+J*EB(x))
L0=lambda x:ca(Z(x)+D(x)/2-2*x)
M0=lambda x:ca(Z(x)+J*B(x))
ES=lambda x:ca(Db(ED(x))-6*ED(x)+ED(D(x)-5*x))
EPE=lambda x:ca(ES(x)+s.diff(EL(x),i)+EA(L0(x)))
EPD=lambda x:ca(4*J*(s.diff(EB(x),J)+EB(B(x)))+2*EB(x)
                +s.diff(EM(x),i)+EA(M0(x)))
EA3=lambda x:ca(s.diff(EA(x),i,2)+s.diff(EA(A(x)),i)+EA(A(A(x))))
S=lambda x:ca(D(D(x)-5*x)-6*(D(x)-5*x))
Sb=lambda x:ca(Db(Db(x)-5*x)-6*(Db(x)-5*x))
PE=lambda x:ca(S(x)+A(L0(x)))
PD=lambda x:ca(4*J*B(B(x))+2*B(x)+A(M0(x)))
PEb=lambda x:ca(Sb(x)+s.diff(Db(x)/2-x,i))
PDb=lambda x:ca(4*J*s.diff(x,J,2)+2*s.diff(x,J)
                +s.diff(x+J*s.diff(x,J),i))
zero(m*D(Q)-Db(m*Q)-s.diff(ED(Q),w),'full D correction')
zero(m*S(Q)-Sb(m*Q)-s.diff(ES(Q),w),'full source correction')
zero(m*PE(Q)-PEb(m*Q)-s.diff(EPE(Q),w),'full PE correction')
zero(m*PD(Q)-PDb(m*Q)-s.diff(EPD(Q),w),'full PD correction')
zero(m*A(A(A(Q)))-s.diff(m*Q,i,3)-s.diff(EA3(Q),w),
     'full A cubed correction')

# The cubic operator identity is checked in its genuine commuting chart.
x,y,z=s.symbols('x y z')
t=s.Function('t')(x,y,z)
aa=lambda f:s.diff(f,x)
bb=lambda f:s.diff(f,y)
zz=lambda f:z*s.diff(f,z)
dd=lambda f:6*zz(f)-2*x*aa(f)-2*y*bb(f)
W=lambda f:z**2*(zz(zz(f)+dd(f)/2+5*f)+y*bb(zz(f)+dd(f)/2+5*f)
                  +2*(zz(f)+dd(f)/2+5*f))
P3=lambda f:aa(aa(aa(f)))+z*(zz(zz(zz(f)+dd(f)/2+f))
                         +y*bb(zz(zz(f)+dd(f)/2+f))
                         +zz(zz(f)+dd(f)/2+f))
zero(P3(z*t)-z*aa(aa(aa(t)))-zz(W(t))+W(t),'literal cubic (Z-1) identity')

# Actual at=t*dlog(v), and its two Laurent-i pieces, without high derivatives.
u=s.symbols('u')
T=1+w**3;N0=9*w**2-16*u*T
L=256*i**2*T**5*N0+729*i**8*u*w**6
vl=64*u*w*N0*T**2/(9*L)
C=s.Function('C')(u,w)
tl=i**-6*w*T*L*C
at=ca(tl*s.diff(vl,w)/vl)
am=256*C*T**5*N0*(1-8*w**3)
ap=729*u*C*(w**6*(w**3-5)+w**7*T*s.diff(N0,w)/N0)
zero(at-i**-4*am-i**2*ap,'actual t dlog v Laurent decomposition')

# A compressed Hermite primitive must check the omitted high coefficients too.
q=w**3-beta*w**2+1
M=s.Matrix(9,9,lambda k,j:s.expand(q*s.diff(w**j,w)-3*s.diff(q,w)*w**j).coeff(w,k))
assert s.factor(M.det())==-362880
checks.append('fixed 9 by 9 Hermite determinant equals minus 9 factorial')

binding=json.loads((HERE/'corrected-rational-source-binding.json').read_text())
canonical=lambda obj:json.dumps(obj,sort_keys=True,separators=(',',':')).encode()
assert hashlib.sha256(canonical(binding['source'])).hexdigest()==binding['source_sha256']
checks.append('authoritative source hash')
hermite=HERE.parent/'ruling-source/adjoint-reconstruction/n-only-hermite-results.json'
data=json.loads(hermite.read_text())
assert data['source_sha256']==binding['source_sha256']
assert data['all_three_full_derivative_identities'] is True
for label in ['i^-1','i^-2','i^-7']:
    c=data['components'][label]
    assert c['simple_remainder_zero'] and c['full_derivative_identity']
    checks.append('independent exact Hermite result bound: '+label)
out={
  'checks':checks,'passed':len(checks),'source_sha256':binding['source_sha256'],
  'n_only_hermite_sha256':hashlib.sha256(hermite.read_bytes()).hexdigest(),
  'primitive':'K=v*(PN+ES(h)-EPE(F)-EPD(G)-EA3(v*t)-W(t)/v)',
  'identity':'Ssrc-PE(F)-PD(G)-P3(v*t)=(Z-1)K',
  'scope':'Constructed scalar rational identity; original curve-valued defect retained',
  'certificate':False,
}
(HERE/'actual-rational-k-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
