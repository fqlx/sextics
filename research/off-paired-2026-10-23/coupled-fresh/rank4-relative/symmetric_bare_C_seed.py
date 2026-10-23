"""Source-derived rational integration trial in symmetric a=1,z=0 fiber.
All operator Jacobians retained. This is not a statement about generic a,z.
"""
import sympy as s
from pathlib import Path
import json
T=s.symbols('T');H=T+2;Nr=2-3*T;r=Nr/H
D=4*T-531441*H**4
# Every function below carries q^-3; E=q*dq therefore acts by -3+6T*dT.
# Formal adjoint of A=(E+4T/H)/r in measure dq.
def Astar(F):return s.cancel(2*F/r-6*T*s.diff(F/r,T)+4*T*F/(r*H))
def aff(F,A,B):return s.cancel(A*Astar(F)+B*F)
def applypoly(F,factors):
 for A,B in factors:F=aff(F,A,B)
 return F
P=[(1,1),(1,1),(2,5),(2,11)]
Q=[(1,0),(1,-1),(1,-3),(1,-4)]
# G=q D A(T)/Nr^3. Monic normalization gives J G=q^-3 Nr A/H^4.
def image(A):
 JG=Nr*A/H**4
 return s.cancel(applypoly(T*JG,P)-531441*applypoly(H**4*JG,Q))
ims=[]
for n in range(3):
 ims.append(image(T**n));print('image',n,'done',flush=True)
# q^-3 times image, source S0=-q^3(2+3T)/(3Nr^2).
forcing=-T*(2+3*T)/(3*Nr**2)
v=s.symbols('v0:3')
expr=s.together(sum(v[n]*ims[n] for n in range(3))+forcing)
num=s.Poly(s.fraction(expr)[0],T)
sol=s.solve(num.all_coeffs(),v,dict=True)
print('solutions',sol,flush=True)
out={'scope':'a=1,z=0 only','G':'q*(4T-531441*(T+2)^4)*sum(v_n*T^n)/(2-3T)^3, T=q^6',
 'equation':'-Lq^*G=S0; S0=-q^3(2+3T)/(3(2-3T)^2)',
 'solutions':[{str(k):str(val) for k,val in x.items()} for x in sol]}
if sol:
 check=s.cancel(sum(sol[0][v[n]]*ims[n] for n in range(3))+forcing)
 assert check==0
out['claim']='Constructive specialized seed trial only; no generic exclusion.'
Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/symmetric-bare-C-seed-results.json').write_text(json.dumps(out,indent=2)+'\n')
