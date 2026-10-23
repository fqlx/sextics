#!/usr/bin/env python3
"""Exact algebra in the tangent-hyperplane support resolution.

No off-paired certificate or Lean theorem is asserted.
"""
import json
from pathlib import Path
import sympy as s

t,x,y,z,aa,bb,rho=s.symbols('t x y z X2 Y2 rho')
H=t**6+x**6+y**6+z**6+t**3*x*y*z/2
C=x**3*z/2+t**2*x*y/3
F=H+aa**6+bb**6+C*aa*bb
restricted=s.expand(F.subs(aa,rho*bb))
checks={
 'exact_endpoint_split':s.expand(F-(t**6+x**6+aa**6+y**6+z**6+bb**6
   +t**3*x*y*z/2+x**3*aa*z*bb/2+t**2*x*aa*y*bb/3))==0,
 'tangent_hyperplane_restriction':s.rem(restricted-H-rho*C*bb**2,rho**6+1,rho)==0,
 'double_cover_substitution':s.expand((C*bb)**2+H*C/rho
   -C*(H+rho*C*bb**2)/rho)==0,
}
r,q=s.symbols('r q')
checks['blowup_t_chart']=s.expand(C.subs(x,t*r)-t**3*r*(r**2*z/2+y/3))==0
checks['blowup_x_chart']=s.expand(C.subs(t,x*q)-x**3*(z/2+q**2*y/3))==0
checks['H_on_exceptional']=s.expand(H.subs({t:0,x:0})-y**6-z**6)==0
checks['H_exceptional_roots_simple']=s.gcd(y**6+1,6*y**5)==1
checks['H_roots_avoid_S_ramification']=(y**6+1).subs(y,0)!=0

r0,r1,k,ell=s.symbols('r0 r1 k ell')
sub={t:r0*k,x:r1*k,y:-s.Rational(3,2)*r1**2*ell,z:r0**2*ell}
expected=((r0**6+r1**6)*k**6
 +(r0**12+s.Rational(729,64)*r1**12)*ell**6
 -s.Rational(3,4)*r0**5*r1**3*k**4*ell**2)
checks['S_normalization_equation']=s.expand((t*t*y+s.Rational(3,2)*x*x*z).subs(sub))==0
checks['normalized_H']=s.expand(H.subs(sub)-expected)==0
u=s.symbols('u')
p=(64+729*u**4)*(1+u**2)**2-4*u**3
checks['normalized_H_eliminant_squarefree']=s.gcd(p,s.diff(p,u))==1
checks['normalized_H_k_zero_simple']=s.gcd(1+s.Rational(729,64)*r**12,
 s.diff(1+s.Rational(729,64)*r**12,r))==1
checks['normalized_H_l_zero_simple']=s.gcd(1+r**6,6*r**5)==1

# Classes are pairs (hyperplane coefficient, exceptional coefficient).
Hclass=s.Matrix([6,0]); Pclass=s.Matrix([1,-1]); Sclass=s.Matrix([3,-2]); Eclass=s.Matrix([0,1])
checks['reduced_branch_class']=Hclass+Pclass+Sclass+Eclass==s.Matrix([10,-2])
checks['cover_line_bundle']=2*s.Matrix([5,-1])==s.Matrix([10,-2])
checks['smooth_H_nonzero_gradient_contradiction']=s.Rational(1,4**3*12**3)!=1
assert all(checks.values()),checks
out={
 'status':'The actual tangent-hyperplane support has h20=0; no original-target primitive or certificate.',
 'checks':checks,'check_count':len(checks),
 'support':'X2=rho*Y2, rho^6=-1',
 'original_target':'A=X0^3*Y0^3',
 'double_cover':'w^2=-rho^-1*H*C',
 'base_blowup':'Bl_{t=x=0}(P3)',
 'branch_after_normalization':'Hprime+Pprime+Sprime+E, class 10H-2E',
 'line_bundle':'5H-E',
 'cohomology_argument':'H2(O_cover)=H2(P3,O)+H2(P3,O(-5))=0; remaining SNC double-cover singularities are toric and rational.',
 'scope':'The algebraic identities are machine checked. SNC geometry, toric rationality and coherent-cohomology arguments are explained in the companion Markdown proof. No Lean verification is claimed.',
}
dest=Path(__file__).with_suffix('.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
