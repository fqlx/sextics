import sympy as s,json
from pathlib import Path
A,h,d,f,g,t,q=s.symbols('A h d f g t q');I4=-h*d*f**2+s.Rational(9,2)*A*h*g*t-g**4/48
I6=-s.Rational(1,4)*(27*A*A*h*h-4*h*d**3)*t*t-A*h*h*f**3+h*d*d*f*g*t+h*d*f*f*g*g/12+s.Rational(5,8)*A*h*g**3*t+g**6/864
x0=s.factor(-s.diff(I6,t).subs(t,0)/s.diff(I4,t));ob=s.factor(x0**3+I4.subs(t,0)*x0+I6.subs(t,0)+4*s.Poly(I6,t).coeff_monomial(t*t));sub={A:1+q**6,d:q/2,g:s.Rational(1,3),f:q*q/(4*(h*h-4))};phys=s.factor(ob.subs(sub));print('I4=',I4);print('I6=',I6);print('x0=',x0);print('genericobstruction=',ob);print('physicalobstruction=',phys);print('q1h3=',phys.subs({q:1,h:3}))
Path('/workspace/research/round6/k3_normalform/constant_section_result.json').write_text(json.dumps({'I4':str(I4),'I6':str(I6),'x0':str(x0),'genericObstruction':str(ob),'physicalObstruction':str(phys),'q1h3':str(phys.subs({q:1,h:3}))},indent=2)+'\n')
