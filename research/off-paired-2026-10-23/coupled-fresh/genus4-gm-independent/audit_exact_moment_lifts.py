#!/usr/bin/env python3
"""Literal full-direction intertwiners and actual polynomial moment preimages."""
import hashlib,json
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent
x,y,z=s.symbols('x y z')
Q=s.Function('Q')(x,y,z)
A=lambda f:s.diff(f,x)
B=lambda f:s.diff(f,y)
Z=lambda f:z*s.diff(f,z)
D=lambda f:6*Z(f)-2*x*A(f)-2*y*B(f)
LE=lambda f:D(D(f)+f)+A(Z(f)+D(f)/2+2*f)
LD=lambda f:4*y*B(B(f))+2*B(f)+A(Z(f)+y*B(f)+f)
L3=lambda f:A(A(A(f)))+z*(Z(Z(Z(f)+D(f)/2+5*f))
                     +y*B(Z(Z(f)+D(f)/2+5*f))
                     +2*Z(Z(f)+D(f)/2+5*f))
PE=lambda f:D(D(f)-5*f)-6*(D(f)-5*f)+A(Z(f)+D(f)/2-2*f)
PD=lambda f:4*y*B(B(f))+2*B(f)+A(Z(f)+y*B(f))
P3=lambda f:A(A(A(f)))+z*(Z(Z(Z(f)+D(f)/2+f))
                     +y*B(Z(Z(f)+D(f)/2+f))
                     +Z(Z(f)+D(f)/2+f))
checks=[]
for label,P,L in [('PE',PE,LE),('PD',PD,LD),('P3',P3,L3)]:
    assert s.expand(P(z*Z(Q))-Z(z*L(Q))+z*L(Q))==0,label
    checks.append('literal unrestricted '+label+' exact-moment intertwiner')

i,u,w=s.symbols('i u w')
K=s.QQ.frac_field(u)
poly=lambda f:s.Poly(f,w,domain=K)
T=1+w**3;N0=9*w**2-16*u*T
pot=json.loads((HERE/'cubic-residue-potentials-results.json').read_text())
rec=pot['actual_Ssrc_residue']
load=lambda ar:sum(s.sympify(c,locals={'u':u})*w**j for j,c in enumerate(ar))
f=poly(load(rec['PE_residue_f_coefficients']))
g=poly(load(rec['PD_residue_g_coefficients']))
crt=poly(load(rec['CRT_factor_coefficients']))
NN=poly(N0);NW=NN.diff()
quotF,remF=(f*NW).div(NN)
quotG,remG=(g*NW).div(NN)
minus=crt*poly(256*T**5*N0*(1-8*w**3))
plus0=crt*poly(729*u*(w**9-5*w**6))
plus1=crt*poly(729*u*w**7*T)*NW
qplus,rplus=plus1.div(NN)
quotHplus=plus0+qplus
def integ(p):
    return s.Poly.from_dict({(j[0]+1,):c/K.convert(j[0]+1)for j,c in p.rep.to_dict().items()},w,domain=K)
def encode(p):return [str(K.to_sympy(c))for c in reversed(p.rep.to_list())]
QF=integ(quotF);QG=integ(quotG);QHm=integ(minus);QHp=integ(quotHplus)
for label,p,q in [('F',quotF,QF),('G',quotG,QG),('Hminus',minus,QHm),('Hplus',quotHplus,QHp)]:
    assert q.diff()==p,label
    checks.append('actual polynomial moment preimage '+label)

# Literal CRT freedom. L0 here is L/i^2; v is allowed a w-independent factor.
L0=256*T**5*N0+729*i**6*u*w**6
vv=64*u*w*N0*T**2/(9*L0)
crit=s.expand(N0*T*L0+w*s.diff(N0,w)*T*L0
              +2*w*N0*s.diff(T,w)*L0-w*N0*T*s.diff(L0,w))
assert s.cancel(crit-w*N0*T*L0*s.diff(vv,w)/vv)==0
checks.append('literal CRT polynomial moment kernel')
critp=s.Poly(crit,w,domain=s.QQ.frac_field(i,u))
cc=[str(critp.nth(j))for j in range(critp.degree()+1)]
binding=json.loads((HERE/'corrected-rational-source-binding.json').read_text())
assert binding['source_sha256']==pot['source_sha256']
out={
  'source_sha256':binding['source_sha256'],
  'authoritative_potential_record':'actual_Ssrc_residue',
  'input_potential_arrays_sha256':hashlib.sha256(json.dumps(rec,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
  'coordinates':'u=J/i^2, N0=9w^2-16u(1+w^3); coefficient arrays are low to high in w',
  'operators':{
    'LE':'D(D+1)+A(Z+D/2+2)',
    'LD':'4JB^2+2B+A(Z+JB+1)',
    'L3':'A^3+v(Z+JB+2)Z(Z+D/2+5)',
  },
  'intertwiners':'PX(v*ZQ)=(Z-1)[v*LX(Q)] for X=E,D,3; alpha(v*ZQ)=d_w Q',
  'moment_preimages':{
    'QF':{'i_weight':-1,'coefficients':encode(QF)},
    'QG':{'i_weight':0,'coefficients':encode(QG)},
    'QH_minus':{'i_weight':-4,'coefficients':encode(QHm)},
    'QH_plus':{'i_weight':2,'coefficients':encode(QHp)},
  },
  'properized_potentials':{
    'F':'Fproper=F-v*ZQF=(v^2/v_w)*i^-1*remF/N0',
    'G':'Gproper=G-v*ZQG=(v^2/v_w)*remG/N0',
    'H':'Hproper=Hpot-v*Z(QH_minus+QH_plus)=(v^2/v_w)*i^2*remH/N0',
    'remF_coefficients':encode(remF),'remG_coefficients':encode(remG),
    'remH_coefficients':encode(rplus),
  },
  'actual_scalar_primitive_shift':'Jproper=K/v+LE(QF)+LD(QG)+L3(QH_minus+QH_plus)',
  'exact_source_retention':'Ssrc-PE(Fproper)-PD(Gproper)-P3(Hproper)=(Z-1)[v*Jproper]',
  'fold_bounds':{
    'original_K_over_v':3,
    'after_full_cubic_properization_K_over_v':5,
    'reason':'QH may have a nonzero linear Morse jet. Hproper acquires a simple fold pole and L3QH may have order5. No fold terms are dropped.',
  },
  'CRT_freedom':{
    'L0':'256T^5*N0+729i^6*u*w^6 = L/i^2',
    'Ccrit_coefficients':cc,
    'change':'Crt -> Crt+N0*g(w), delta_t=i^-4*w*T*L0*N0*g',
    'Q_explicit':'For g=sum(g_m*w^m), Q=i^-4*sum_{k,m} Ccrit_k*g_m*w^(k+m+1)/(k+m+1)',
    'identity':'delta_t=ZQ; delta_Hpot=vZQ; delta(K/v)=-L3Q',
    'scope':'Polynomial g over the coefficient field; no unevaluated primitive and no new N residue',
  },
  'checks':checks,'passed':len(checks),'certificate':False,
  'scope':'Actual source-bound scalar lift changes. Every compact and infinity curve defect row remains; no global fold cancellation is asserted.',
}
path=HERE/'actual-polynomial-moment-preimages.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                  'Q_degrees':{name:p.degree()for name,p in [('QF',QF),('QG',QG),('QH_minus',QHm),('QH_plus',QHp)]},
                  'fold_bound_after_full_properization':5},indent=2))
