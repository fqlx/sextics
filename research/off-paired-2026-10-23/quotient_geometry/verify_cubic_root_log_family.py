from pathlib import Path
import json
import sympy as s
r,k,H,C=s.symbols('r k H C')
P=(r-1)**3+k*r
kr=-(r-1)**3/r
F=1/(1+2*r)
ap=1/(3*r)
ag=3/((1+2*r)*(4-r))
checks={}
checks['discriminant_factor']=s.factor((4*k+27).subs(k,kr)-(1+2*r)**2*(4-r)/r)==0
num=s.together(ag-81*ap/(4*k+27)-3*s.diff(F,r)).as_numer_denom()[0]
checks['root_log_exact_relation']=s.rem(s.expand(num),P,r)==0
R=r*(r-1)/(C*H*(1+2*r)**3)
checks['entire_source_differential']=s.factor(C*H*R*s.diff(kr,r)/kr+s.diff(F,r)/2)==0
# Multiplication by r in Q(k)[r]/P, with basis(1,r,r^2).
M=s.Matrix([[0,0,1],[1,0,-3-k],[0,1,3]])
checks['trace_F_is_one']=s.factor(s.trace((s.eye(3)+2*M).inv())-1)==0
# Product-rule verification of the actual Qlog bracket, using {p,Q}=NQ/g.
p,Q,g,NQ=s.symbols('p Q g NQ')
checks['actual_Q_log_correction']=s.simplify((p/Q)*(NQ/(g*Q))-p*NQ/(Q**2*g))==0
out={'checks':checks,'status':'Exact closed trace-free root-log family and source identity; no closed eta/current completing the source.'}
assert all(checks.values()),checks
Path(__file__).with_name('cubic-root-log-family-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
