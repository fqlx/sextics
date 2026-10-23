from pathlib import Path
import sympy as s,json,pickle
here=Path(__file__).parent;u=s.symbols('u')
P=s.Rational(1,81)+s.Rational(40,9)*u-10368*u**3-186624*u**4
S2=s.expand(P/9);T=-8*u-144*u*u
A=s.factor(-27*S2);B=s.factor(-27*(T**3-T/s.Integer(243)-u*u*S2/64-s.Rational(2,19683)))
D=s.factor(-16*(4*A**3+27*B**2));g=s.gcd(A,B)
print('9S2',s.factor(P));print('A',A);print('B',B);print('Delta',D);print('gcd',g)
print('quartic_discriminant',s.factor(s.discriminant(P,u)))
# Invariance of the exact displayed weighted-exceptional model.
H,SS=s.symbols('H SS');f=9*SS**6-SS**4/s.Integer(81)-s.Rational(40,9)*H*SS**3+10368*H**3*SS+186624*H**4
assert s.expand(f.subs(H,u*SS)/SS**4-(9*SS**2-P))==0
out={'variables':('u',),'S_squared':str(S2),'A':str(A),'B':str(B),'Delta':str(D),'gcd_A_B':str(g),'quartic_discriminant':str(s.factor(s.discriminant(P,u))),'genus1_quartic_squarefree':s.degree(s.gcd(P,s.diff(P,u)),u)==0,'A_degree':s.degree(A,u),'B_degree':s.degree(B,u),'D_degree':s.degree(D,u)}
out.update(branch_bad_fiber_gcd=str(s.gcd(P,D)),discriminant_squarefree=s.degree(s.gcd(D,s.diff(D,u)),u)==0)
(here/'elliptic_basechange.pickle').write_bytes(pickle.dumps(dict(u=u,P=P,S2=S2,A=A,B=B,D=D)))
(here/'elliptic_basechange.json').write_text(json.dumps(out,indent=2,default=str)+'\n')
