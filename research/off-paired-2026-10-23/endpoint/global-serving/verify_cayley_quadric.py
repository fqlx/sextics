#!/usr/bin/env python3
"""Exact global Cayley quadric/source identities; no certificate claim."""
import itertools
import json
from collections import Counter
from pathlib import Path
import sympy as s

a,b,U,V,q,p,w,z,l,m,n=s.symbols('a b U V q p w z l m n')
Dl=n*n-l*l/4
Dm=n*n-m*m/4
H0=w**6+z**6+w**3*z*q/2+w*w*q*p/3
C1=a*b-q**3
C2=U*V-p**3
Q=a*a+b*b+U*U+V*V+H0+a*z*p/2
F=l*C1+m*C2+n*Q
S=n*H0-l*q**3-m*p**3
F0=Dl*S-n**3*z*z*p*p/16
Se=F0/Dl
a0=-n*n*z*p/(4*Dl)
b0=l*n*z*p/(8*Dl)
fiber=[a,b,U,V]
xc=[a-a0,b-b0,U,V]
checks=[]
def check(name,expr):
    ok=s.cancel(expr)==0
    checks.append({'name':name,'passed':bool(ok)})
    if not ok:raise AssertionError((name,s.factor(expr)))

M=s.Matrix([[n,l/2,0,0],[l/2,n,0,0],[0,0,n,m/2],[0,0,m/2,n]])
check('rank-four determinant',M.det()-Dl*Dm)
check('completed square',F-((s.Matrix(xc).T*M*s.Matrix(xc))[0]+Se))
M5=s.zeros(5)
M5[:4,:4]=M
M5[0,4]=M5[4,0]=n*z*p/4
M5[4,4]=S
check('compact quadric determinant',M5.det()-Dm*F0)

Tv=[-l/(4*Dl),n/(2*Dl),0,0]
check('odd field derivative',sum(Tv[i]*s.diff(F,fiber[i]) for i in range(4))-(b-b0))
check('odd field divergence',sum(s.diff(Tv[i],fiber[i]) for i in range(4)))
check('centered Euler',sum(xc[i]*s.diff(F,fiber[i]) for i in range(4))-2*(F-Se))
check('centered Euler divergence',sum(s.diff(xc[i],fiber[i]) for i in range(4))-4)
def div(v):return sum(s.diff(v[i],fiber[i]) for i in range(4))
# Clear only the formal scalar denominator first. Expanding F**4 before
# differentiation would make this small exact identity needlessly costly.
ff,ss,xf=s.symbols('ff ss xf')
check('pole-three homotopy',(4*ff-2*xf-4*ss).subs(xf,2*(ff-ss)))
check('pole-four homotopy',(8*ss*ff-6*ss*xf+4*ff**2-2*ff*xf-12*ss**2).subs(xf,2*(ff-ss)))
P=[-n*w**3*Tv[i]/(3*F**3)+n*w**3*b0*(xc[i]/(6*Se*F**3)+xc[i]/(12*Se**2*F**2)) for i in range(4)]
check('actual Cayley numerator partial primitive',n*w**3*((b-b0)+b0-b))
check('critical support coefficient',n*w**3*b0/(12*Se**2)-l*n*n*z*p*w**3*Dl/(96*F0**2))

yi={b:-b,V:-V,q:-q,p:-p,z:-z,l:-l,m:-m}
for name,poly,sign in [('C1',C1,-1),('C2',C2,-1),('Q',Q,1),('F',F,1),('Dl',Dl,1),('Dm',Dm,1),('F0',F0,1)]:
    check('Y involution '+name,poly.xreplace(yi)-sign*poly)
check('source numerator Y character',(n*w**3*b).xreplace(yi)+n*w**3*b)
check('main source coefficient Y character',(l*n*n*z*p*w**3*Dl).xreplace(yi)+l*n*n*z*p*w**3*Dl)

group=[]
for tail in itertools.product(range(6),repeat=5):
    e=(0,)+tail
    if ((3*e[0]+e[1]+e[3]+e[4])%6==0 and
        (3*e[1]+e[2]+e[4]+e[5])%6==0 and
        (2*e[0]+e[1]+e[2]+e[3]+e[5])%6==0):group.append(e)
assert len(group)==36
assert {sum(e)%6 for e in group}=={0,3}
ages=Counter()
for e in group:
    assert (4*e[0]+e[1]+e[2]+4*e[3]+e[4]+e[5])%6==0
    if not any(e):continue
    for phase,count in Counter(e).items():
        if count>=2:
            age6=sum((x-phase)%6 for x in e)
            assert age6>=6
            ages[age6]+=1
checks.append({'name':'full projective diagonal group/source character/Reid-Tai ages','passed':True})
out={'status':'exact identities only; no full primitive or serving theorem',
     'checks':checks,'passed':len(checks),
     'diagonal_group_order':len(group),'ages_in_sixths':dict(sorted(ages.items())),
     'source_partial_current':[str(x) for x in P],
     'main_critical_coefficient':str(l*n*n*z*p*w**3*Dl/(96*F0**2)),
     'normalization_warning':'Cayley factorial and final quadric-cylinder normalization have not been bound to the original certificate.'}
dest=Path(__file__).with_name('cayley-quadric-results.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'diagonal_group_order':len(group),'age_sixths':dict(sorted(ages.items()))}))
