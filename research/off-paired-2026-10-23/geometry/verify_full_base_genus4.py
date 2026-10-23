import json
from pathlib import Path
import sympy as s
t,u,b,k=s.symbols('t u b kappa')
B=-k**2
Q=-t**2+b*t+B
f=u**6-t**2*Q
checks={}
checks['sigma_curve']=s.cancel((k*u/t)**6-(k**2/t)**2*Q.subs(t,k**2/t)-k**6/t**6*f)==0
w=u**2/t
for sign,label in ((1,'plus'),(-1,'minus')):
 Y=u*(1+sign*k/t)
 checks['j0_quotient_'+label]=s.rem(s.together(Y**2-w*(b+sign*2*k-w**3)).as_numer_denom()[0],f,u)==0
 X=1/w;W=Y/w**2
 du=u*(s.Rational(1,3)/t+s.diff(Q,t)/(6*Q))
 deriv=lambda e:s.diff(e,t)+s.diff(e,u)*du
 rhs=t*(t-sign*k)/(3*u**5)
 checks['j0_differential_'+label]=s.rem(s.together(deriv(X)/W-rhs).as_numer_denom()[0],f,u)==0
R=t+B/t
checks['genus2_quotient']=s.rem(s.together(R**2-(w**3-b)**2-4*B).as_numer_denom()[0],f,u)==0
checks['genus2_differential']=s.rem(s.together(deriv(w)/R+t/(3*u**4)).as_numer_denom()[0],f,u)==0
checks['source_differential']=s.rem(s.together(w*deriv(w)/R+1/(3*u**2)).as_numer_denom()[0],f,u)==0
checks['source_sigma_sign']=s.cancel((-k**2/t**2)/(k*u/t)**2+1/u**2)==0
assert all(checks.values()),checks
out={'checks':checks,'status':'Exact coefficient-retaining curve and differential identities; no kernel descent or certificate.'}
Path(__file__).with_name('full-base-genus4-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
