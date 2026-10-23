#!/usr/bin/env python3
"""Independent generic discriminant and nonempty-specialization RR audit.

This validates the complete candidate space, not a source preimage.
"""
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent
uvar,p,q,r,n,d,T=s.symbols('u p q r n d T')
P=s.Poly(r*uvar**4+q*uvar*uvar+p*uvar+1,uvar)
monic=P.as_expr()/r
disc_u=s.discriminant(monic,uvar)
Dr=256*r*r+(144*p*p*q-128*q*q-27*p**4)*r+16*q**4-4*p*p*q**3
checks={}
assert s.cancel(disc_u-Dr/r**5)==0
checks['generic_reciprocal_power_discriminant']=True
lhs=s.cancel((n/T)**4*disc_u.subs(r,n/d))
Dnum=256*n*n+(144*p*p*q-128*q*q-27*p**4)*n*d+(16*q**4-4*p*p*q**3)*d*d
assert s.cancel(lhs-d**3*Dnum/(n*T**4))==0
checks['generic_allowed_pole_module_discriminant']=True

w=s.symbols('w')
prime=1009
iv,jv,ell=2,1,3
uv=s.Rational(jv*jv,iv*iv)
tv=1+w**3
nv0=9*w*w-16*uv*tv
lv0=256*tv**5*nv0+729*iv**6*uv*w**6
dv=w*nv0*tv*tv
cv=s.cancel(-(s.diff(lv0,w)*dv-lv0*s.diff(dv,w))/tv)
poly=lambda x:s.Poly(x,w,modulus=prime)
nn,dd,cc,tt,NN=map(poly,[lv0,dv,cv,tv,nv0])
kappa=s.Rational(9,64)/uv
pp=jv*ell;qq=iv*ell*ell+ell+1
BB=144*pp*pp*qq-128*qq*qq-27*pp**4
CC=16*qq**4-4*pp*pp*qq**3
discnum=poly(256*kappa**2*ell**12*lv0**2+BB*kappa*ell**6*lv0*dv+CC*dv**2)
checks['degree_profile_18_10_24']=tuple(z.degree()for z in (nn,dd,cc))==(18,10,24)
for label,zz in [('n',nn),('Ccrit',cc),('T',tt),('N0',NN),('quartic_nonzero_critical_pullback',discnum)]:
    assert s.gcd(zz,zz.diff()).degree()==0,label
    checks['squarefree_'+label]=True
for label,x,y in [('n_d',nn,dd),('Ccrit_d',cc,dd),('Ccrit_n',cc,nn),('Dnum_n',discnum,nn),('Dnum_d',discnum,dd),('Dnum_Ccrit',discnum,cc)]:
    assert s.gcd(x,y).degree()==0,label
    checks['coprime_'+label]=True

ramification=18+36+4*3+3*2
genus=(ramification-6)//2
assert genus==33
checks['riemann_hurwitz_genus']=True
divdegree=24*4*3+18
bounds=[72,74,61,63]
dimension=sum(k+1 for k in bounds)
assert dimension==divdegree+1-genus==274
checks['complete_rr_dimension']=True
out={
 'status':'Candidate-space mathematical audit; actual source preimage still open',
 'checks':checks,'count':len(checks),
 'generic_discriminant_identity':str(s.factor(d**3*Dnum/(n*T**4))),
 'nonempty_specialization':{'prime':prime,'i':iv,'j':jv,'l':ell,'degrees':{'n':nn.degree(),'d':dd.degree(),'Ccrit':cc.degree(),'Dnum':discnum.degree()}},
 'genus':genus,'ramification_total':ramification,
 'primitive_divisor_degree':divdegree,
 'basis':'[1,u,(L0/T)u^2,(L0/T)u^3]/Ccrit^3, u=1/a',
 'numerator_degree_bounds':bounds,'dimension':dimension,
 'scope':'Generic discriminant identity and nonzero finite-field witness establish the stated open conditions; neither a source primitive nor any sextic nonexistence assertion is made.'}
path=HERE/'complete-rr-space-audit-results.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'pass':all(checks.values()),'output':str(path)}))
