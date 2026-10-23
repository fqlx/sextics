"""Relative Klein kernel and both graph branches, with explicit scope/signs."""
import sympy as s
import json
from pathlib import Path
p,q,H,C,Zp,Zq,D,B=s.symbols('p q H C Zp Zq D B')
f=lambda t:(H+C*t)**2-4*t**6
polar=2*H**2+2*H*C*(p+q)+2*C*C*p*q-8*p**3*q**3
assert s.expand(polar.subs(p,q)-2*f(q))==0
assert s.expand(polar-2*f(q)-(p-q)*s.diff(f(q),q)
                +8*q**3*(p-q)**2*(p+2*q))==0
K=(Zp+Zq)/(2*Zp*(p-q))
Kq=s.diff(K,q)+s.diff(K,Zq)*s.diff(f(q),q)/(2*Zq)
Bidiff=(polar+2*Zp*Zq)/(4*(p-q)**2*Zp*Zq)
error=s.together(Bidiff-Kq+2*p*q**3/(Zp*Zq)+4*q**4/(Zp*Zq))
num=s.fraction(error)[0]
assert s.Poly(num,Zq).rem(s.Poly(Zq**2-f(q),Zq)).as_expr().expand()==0

r=H*B/(D*C)
mu=B**3*H**2/(D**2*C**3)
assert s.cancel(r**3*D-mu*H)==0
assert s.cancel(r**2*B-mu*C)==0
scaled=(D+B*q)**2-4*q**6
assert s.cancel(f(r*q)-r**6*scaled-(1-mu**2)*(H+C*r*q)**2)==0

result={'status':'passed','exact_groups':6,
        'kernel_scope':'Relative bidifferential coefficient identities, not a globally closed H20 residue or source primitive.',
        'sign':'Kq is the bidifferential coefficient partial_q(Kp); exterior d(Kp dp) has -Kq dp wedge dq.',
        'full_graph':'(D^2*C^3-B^3*H^2)*(D^2*C^3+B^3*H^2)=0; both signs give the same hyperelliptic polynomial after rational rescaling.',
        'warning':'An exact form d(tau) is a correction kernel and cannot alone carry a nonzero proper H20 residue class.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
