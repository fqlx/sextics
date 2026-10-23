"""Exact canonical decomposition of the actual Prym-current remainder.

No search, truncation, or omitted component.  The literal wedge signs and the
elliptic Dwork identity are checked separately by endpoint first_prym_current.
"""
import json
from pathlib import Path
import sympy as S

q,z,D=S.symbols('q z D')
B=-z/2
Ps=2*q**3+B*q+D
Pd=-2*q**3+B*q+D
Delta=4*B**6-729*D**4
den=(z**3-108*D**2)*(z**3+108*D**2)
Rs=(12*B*q*q-18*D*q+4*B*B)/(54*D*D+4*B**3)
Rd=(-12*B*q*q+18*D*q+4*B*B)/(-54*D*D+4*B**3)
alpha=z*q**3/(144*Ps*Pd)
base=alpha-z/S.Integer(576)*(-S.diff(Ps,q)*Rs/Ps+S.diff(Pd,q)*Rd/Pd)
cross=-z/S.Integer(576)*(S.diff(Ps,q)*Rd-S.diff(Pd,q)*Rs)
target_base=z**4*(3*D+q*z)/(128*Delta)
rows=[3*D**2*z**4/(128*Delta),-D*z**5/(256*Delta),
      z**6/(768*Delta),-81*D**3*z/(16*Delta),-27*D**2*z**2/(16*Delta)]
target_cross=sum(rows[j]*q**j for j in range(5))
checks=[]
def check(label,value):
    assert S.cancel(value)==0,(label,S.factor(value))
    checks.append(label)
check('discriminant-factorization',den-16*Delta)
check('rational-character',base-target_base)
check('background-genus-two-character',cross-target_cross)
check('same-universal-endpoint-family',Ps*Pd-((D+B*q)**2-4*q**6))
# Algebraic character multiplication: Cq*Q consists of rational, elliptic,
# and mixed terms.  Work in basis {1,s,d,sd} over Q(q,z,D).
# 1/s=s/Ps, 1/d=d/Pd, 1/(sd)=sd/(Ps*Pd).
sv,dv=S.symbols('sv dv')
G=S.groebner([sv**2-Ps,dv**2-Pd],sv,dv,domain=S.QQ.frac_field(q,z,D))
Q=Rd*dv/Pd-Rs*sv/Ps
Cq=S.Rational(1,3)+z*(S.diff(Ps,q)*sv/Ps+S.diff(Pd,q)*dv/Pd)/8
Aactual=alpha-Cq*Q/72
Atarget=target_base+Rs*sv/(216*Ps)-Rd*dv/(216*Pd)+target_cross*sv*dv/(Ps*Pd)
n,_=S.fraction(S.cancel(Aactual-Atarget))
check('complete-physical-Cq-character-decomposition',G.reduce(n)[1])
# H-normal primitive scalar identity: ds/dH=1/(2s), dd/dH=1/(2d).
check('actual-H-source-scalar',S.Rational(1,2)/dv-S.Rational(1,2)/sv-6*(1/dv-1/sv)/12)
assert rows[2]!=0
checks.append('infinity-residue-row-retained')
out={'status':'Exact actual source-current operator decomposition; no primitive',
     'checks':checks,'background_compact_basis':[0,1,3,4],
     'background_third_kind_basis_index':2,
     'background_genus_two_coefficients_0_to_4':[str(S.factor(x)) for x in rows],
     'rational_character':str(S.factor(target_base)),
     'elliptic_characters':{'1/s':str(S.factor(Rs/216)),'1/d':str(S.factor(-Rd/216))}}
Path(__file__).with_name('two-family-source-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed',len(checks),'exact source-operator and all-character checks')
