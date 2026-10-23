"""Exact principal-source fold match and a generic nonzero-resultant witness.

This verifies a forced leading current, not the lower-pole source remainder.
"""
import json
from pathlib import Path
import sympy as s
w,i,J=s.symbols('w i J')
p=1009
T=1+w**3
N=9*i*i*w*w-16*J*T
M=256*T**5*N+729*i**6*J*w**6
Afull=9*i*i*M
Bfull=-64*J*w*T*T*N
generic_C=s.Poly(s.diff(Bfull,w)*Afull-s.diff(Afull,w)*Bfull,w)
generic_C,division_remainder=s.div(generic_C,s.Poly(T,w))
assert division_remainder.is_zero and generic_C.degree()==24
point={i:s.Rational(8,3),J:1}
def poly(expr):
    f=s.Poly(s.expand(expr.subs(point)),w)
    return s.Poly.from_dict({m:int(c.p)%p*pow(int(c.q),-1,p)%p
                            for m,c in f.terms()},w,modulus=p)
A,B=poly(Afull),poly(Bfull)
Ai,Bi,AJ,BJ=[poly(s.diff(f,x)) for f,x in
             [(Afull,i),(Bfull,i),(Afull,J),(Bfull,J)]]
U=Bi*A-Ai*B
V=BJ*A-AJ*B
C=B.diff()*A-A.diff()*B
coordinate_boundary=poly(w*T*N*M)
removed=[]
while True:
    divisor=s.gcd(C,coordinate_boundary)
    if divisor.degree()==0:
        break
    removed.append(divisor.degree())
    C=C.exquo(divisor)
C=C.monic()
assert C==poly(generic_C.as_expr()).monic()
ip=8*pow(3,-1,p)%p
jp=1
K1=-B*A+jp*V
K3=-4*B*A-ip*U-jp*V
Q=(U**3+B**2*K1*K3).rem(C)
KD=-6*B*A-2*ip*U-2*jp*V
F=(-3456*ip**3*B*poly(w*w*T**3)*KD**2).rem(C)
assert C.degree()==24
assert s.gcd(C,Q).degree()==0
assert s.gcd(C,C.diff()).degree()==0
assert s.gcd(C,poly(N)).degree()==0
sigma_one=(KD**2+U*K3).rem(C)
sigma_two=(4*jp*V**2+U*K1).rem(C)
assert s.gcd(C,sigma_one).degree()==0
assert s.gcd(C,sigma_two).degree()==0
inverse=s.invert(Q,C)
Gw=(F*inverse).rem(C)
assert (Q*Gw-F).rem(C).is_zero
G=s.Poly.from_dict({(n[0]+1,):int(c)*pow(n[0]+1,-1,p)%p
                    for n,c in Gw.terms()},w,modulus=p)
assert G.diff()==Gw
# Preserve the already served N residue while matching the forced fold jet.
Qfixed=poly(N)**2
Hermite_inverse=s.invert((Qfixed*C.diff()).rem(C),C)
Hermite_factor=(Gw*Hermite_inverse).rem(C)
Gcrt=Qfixed*C*Hermite_factor
assert (Gcrt.diff()-Gw).rem(C).is_zero
assert (Q*Gcrt.diff()-F).rem(C).is_zero
assert Gcrt.rem(Qfixed).is_zero
def ascending(f):
    return [int(f.nth(n))%p for n in range(f.degree()+1)]
out={'status':'passed','prime':p,'point':{'i':'8/3','J':'1'},
     'critical_degree':C.degree(),'removed_boundary_factor_degrees':removed,
     'generic_nonzero_resultant_witness':True,
     'critical_polynomial_ascending':ascending(C),
     'principal_symbol_mod_critical':ascending(Q),
     'inverse_mod_critical':ascending(inverse),
     'forced_G_derivative':ascending(Gw),'forced_G_moment':ascending(G),
     'critical_squarefree':True,'critical_coprime_N':True,
     'quadratic_symbols_invertible_mod_critical':[True,True],
     'N_squared_preserving_CRT_moment':ascending(Gcrt),
     'CRT_moment_degree':Gcrt.degree(),
     'source_convention':'positive R=(D-6)(D-5)hsrc; negate for the -Hsrc_ee Green reconstruction',
     'scope':'Nonzero specialization proves generic principal inverse exists. Source leading-fold polynomial identity and integrated moment pass modulo1009. Lower fold poles and regular source remainder are not cancelled; no certificate.',
     'certificate':False}
Path(__file__).with_name('fold-symbol-witness-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','prime','point','critical_degree','generic_nonzero_resultant_witness','certificate']}))
