#!/usr/bin/env python3
"""Independent full-base Pa serving and source-preserving compact reduction.

This does not integrate the remaining compact source. All signs refer to
positive Ssrc; the original source uses the opposite overall sign.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

c,d,e,q,b=s.symbols('c d e q b')
coordinates=(c,d,e)
f,g,h,H,M,chi=[s.Function(n)(c,d,e) for n in ('f','g','h','H','M','chi')]
av=(-c/3,-2*d/3,-e/6)
bv=(-c/3,-d/6,-e/6)
tv=(-c/3,-d/6,-2*e/3)
zv=tuple(-v for v in bv)
checks={}


def act(v,x):return sum(a*s.diff(x,y) for a,y in zip(v,coordinates))
def div(v):return sum(s.diff(a,y) for a,y in zip(v,coordinates))
def add(*vs):return [sum(v[j] for v in vs) for j in range(3)]
def times(x,v):return [x*a for a in v]
def check(name,x):
    x=s.expand(x)
    assert x==0,(name,x)
    checks[name]=True


def adjE(x):return s.diff(x,e,2)-s.diff(act(tv,x)-4*x/3,c)
def adjD(x):return s.diff(x,d,2)-s.diff(act(av,x)-5*x/6,c)
def adj3(x):
    y=act(tv,x)-5*x/3
    y=act(bv,y)-y/6
    y=act(av,y)-7*y/6
    return s.diff(x,c,3)-y


S=-act(av,h)+7*h/6
T=-act(bv,S)+S/6
BE=[act(tv,f)-4*f/3,0,-s.diff(f,e)]
BD=[act(av,g)-5*g/6,-s.diff(g,d),0]
B3=add(times(-h/4,av),times(S/2,bv),times(T,tv),[-s.diff(h,c,2),0,0])
check('PE scalar Green current at constant residue',div(BE)+adjE(f))
check('PD scalar Green current at constant residue',div(BD)+adjD(g))
check('P3 scalar Green current at constant residue',div(B3)+adj3(h))
V=add([0,0,s.diff(H,e)],BE,BD,B3)
check('full positive source reduction divergence',
      div(V)-s.diff(H,e,2)+adjE(f)+adjD(g)+adj3(h))
X=add(V,times(-M,zv))
kernel=M*(act(bv,chi)-chi/2)
compact_current=div(times(chi,X))-act(V,chi)
compatibility=s.diff(H,e,2)-adjE(f)-adjD(g)-adj3(h)-div(times(M,zv))+M/2
check('literal kernel to compact product rule',compact_current-kernel-chi*compatibility)
check('Z volume divergence',div(zv)-s.Rational(2,3))

# The actual K binding supplies compatibility=0, through
# H_ee-sum(P*pot)=e^-7(Z-1)K and M=e^-7K.
k=s.Function('K')(c,d,e)
mm=e**(-7)*k
check('actual weight restores one half correction',
      div(times(mm,zv))-e**(-7)*(act(zv,k)-k)-mm/2)

# Independently verify all three implicit fiber derivatives, without importing
# the primary normal-function implementation.
P=b**4+(c*q*q+e*q+1)*b*b+d*q**4*b+q**6
Pb=s.diff(P,b)
J=2*q**6/b**2+d*q**4/b-2*b*b
zeta=b/q
for par,num in ((c,b*q),(d,q**3),(e,b)):
    derivative=s.diff(zeta,par)-s.diff(P,par)*s.diff(zeta,b)/Pb
    expression=s.cancel(derivative-num/J)
    numerator=expression.as_numer_denom()[0]
    check('literal compact first derivative '+str(par),s.rem(numerator,P,b))

# Exact fingerprints for arbitrary monomial exponents. These are polynomial
# identities in the exponents, so they cover every rational input by Leibniz.
m,n,r=s.symbols('m n r')
D=6*r-2*m-2*n
check('F c-current weight',m+n-4*r+2-(-r-D/2+2))
check('F e-current weight',-(-5-2*m-2*n+6*r)+(D-5))
check('G c-current weight',(-n-r)-(-r-n))
check('H Astar weight',-(-n-r+s.Rational(1,6))+s.Rational(7,6)-(r+n+1))
check('H Bstar Astar weight',-(-r+s.Rational(1,6))*(r+n+1)+(r+n+1)/6-r*(r+n+1))

root=Path(__file__).resolve().parents[2]
binding=root/'coupled-fresh/genus4-gm-independent/corrected-rational-source-binding.json'
out={
 'status':'Exact source-preserving compact-only three-row forcing; primitive open',
 'source_binding_sha256':hashlib.sha256(binding.read_bytes()).hexdigest(),
 'convention':'positive Ssrc; negate full reconstruction for original source',
 'weights':'f=e^-5F, g=e^-5G, h=e^-1Hpot, Hsrc=e^-5hsrc, M=e^-7K',
 'X':'Hsrc_e E+B_PE(f,1)+B_PD(g,1)+B_P3(h,1)-M Z',
 'Pa_primitive':'±sqrt(-1) contraction(X,dc wedge dd wedge de)',
 'Pa_source':'±sqrt(-1) K di wedge dj wedge dh/6, h=e^-3',
 'compact_identity':'M(B0-1/2)zeta=div(X*zeta)-V_c*zeta_c-V_d*zeta_d-V_e*zeta_e',
 'compact_differentials':{'zeta_c':'b*q*dq/J','zeta_d':'q^3*dq/J','zeta_e':'b*dq/J'},
 'rational_auxiliary_S':'(Z+J*B+1)Hpot',
 'rational_auxiliary_T':'Z*S',
 'C':'(-Z-D/2+2)F-(Z+J*B)G-A^2 Hpot+i*v*(Hpot/12-S/6-T/3)',
 'Dbar':'-2*B G+v*(Hpot/6-S/12-T/6)',
 'Ebar':'(D-5)(hsrc-F)+v*(Hpot/24-S/12-2*T/3)',
 'normalized_vector':'V_c=e^-5 C, V_d=j*e^-6 Dbar, V_e=e^-6 Ebar',
 'rational_w_forcing':'-v_w/(12*j*v^2)*(C*beta_bq+j*Dbar*beta_q3+Ebar*beta_b), j^2=J',
 'scope':'All finite and infinity residues of the remaining compact source are zero. The complete compact rational primitive remains to be constructed. This does not establish a sextic certificate.',
 'checks':checks,'count':len(checks)
}
path=Path(__file__).with_name('compact-three-row-source-results.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'pass':True,'checks':len(checks),'output':str(path)}))
