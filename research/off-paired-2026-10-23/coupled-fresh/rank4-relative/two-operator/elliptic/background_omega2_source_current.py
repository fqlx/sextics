"""Source-directed all-component current for the mixed genus-two character.

Exact background Dwork reduction plus endpoint Leibniz corrections. No fiber
restriction and no integration assertion for the displayed remainder.
"""
import json
from pathlib import Path
import sympy as S
q,z,D=S.symbols('q z D')
B=-z/2
Delta=4*B**6-729*D**4
P=(D+B*q)**2-4*q**6
jlist=[0,1,3,4]
cD=S.Matrix([6*B**4*D,-2*B**5,162*B*D**2,-216*B**2*D])/Delta
Rnum=[-18*B**3*D**2,-24*B**4*D,-2*B**5,243*D**3,-162*B*D**2,108*B**2*D]
R=sum(x*q**j for j,x in enumerate(Rnum))/Delta
lam=z**6/(768*Delta)
p5=S.Matrix([3*D**2*z**4/128,-D*z**5/256,z**6/768,-81*D**3*z/16,-27*D**2*z**2/16])/Delta
remaining=S.Matrix([0,-D*z**5/(128*Delta),0,27*D**2*z**2/(16*Delta)])
checks=[]
def check(label,value):
    if isinstance(value,S.MatrixBase):
        assert all(S.cancel(x)==0 for x in value),(label,value)
    else:
        assert S.cancel(value)==0,(label,S.factor(value))
    checks.append(label)
check('background-third-kind-D-column-polynomial-Dwork',
      -q*q*(D+B*q)-sum(cD[k]*q**j for k,j in enumerate(jlist))*P
      -S.diff(R,q)*P+R*S.diff(P,q)/2)
check('actual-source-compact-column-match',
      S.Matrix([p5[j] for j in jlist])-D*cD/16-remaining)
check('actual-source-infinity-column',p5[2]-lam)
# Use w symbol solely to check all physical endpoint derivative corrections.
w,CH,Cq,F,FH,FC=S.symbols('w CH Cq F FH FC')
o2=q*q/w
o2H=-q*q*(D+B*q)/w**3
Rq=S.diff(R,q)/w-R*S.diff(P,q)/(2*w**3)
bgcompact=sum(cD[k]*q**j for k,j in enumerate(jlist))/w
# The background equality is already proved polynomially.  This is its
# all-component Leibniz consequence, with FH and FC arbitrary vectors.
source=(D*bgcompact/16+lam*o2+sum(remaining[k]*q**j for k,j in enumerate(jlist))/w)*F
divH=(o2*F+D*o2H*F+D*o2*(FH+CH*FC))/16
divq=-D*(Rq*F+R*Cq*FC/w)/16
residual=((lam-S.Rational(1,16))*o2+sum(remaining[k]*q**j for k,j in enumerate(jlist))/w)*F-D*o2*(FH+CH*FC)/16+D*R*Cq*FC/(16*w)
num,_=S.fraction(S.cancel((source-divH-divq-residual)*w**3))
check('complete-physical-endpoint-Leibniz-corrections',S.rem(num,S.Poly(w*w-P,w).as_expr(),w))
out={'status':'Exact mixed-source H/q partial current; full residual retained',
     'checks':checks,'source_compact_match_coefficient':'D/16',
     'background_third_kind_primitive_R':str(S.factor(R)),
     'background_compact_residual_0_1_3_4':[str(S.factor(x)) for x in remaining],
     'lambda':str(S.factor(lam)),
     'coefficient_currents':{'H':'D*q^2*F/(16*w)','q':'-D*R*F/(16*w)'},
     'literal_currents':'-D*q^2*F^dq^dz/(16*w)-D*R*F^dH^dz/(16*w)',
     'endpoint':'F=∇C omega0; FH=∇H∇C omega0, FC=∇C² omega0, all universal parameter derivatives before pullback',
     'physical_derivatives':'∇Hphys F=FH+C_H FC; ∇qphys F=C_q FC',
     'residual':'[(lambda-1/16)*q^2/w-D*z^5*q/(128*Delta*w)+27*D^2*z^2*q^4/(16*Delta*w)]*F-D*q^2*(FH+C_H*FC)/(16*w)+D*R*C_q*FC/(16*w)'}
Path(__file__).with_name('background-omega2-source-current.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed',len(checks),'exact background-column and full endpoint-current checks')
