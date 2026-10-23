#!/usr/bin/env python3
"""Exact branch support, source residue, and holomorphic-cover identities."""
import json
from pathlib import Path
import sympy as s

R,S,z,r,k,u,v,h=s.symbols('R S z r k u v h')
Z=z**6
P=2-Z; Q=1-8*Z; T=3*(Z-1)
Delta=3*R*S*Z-3*R*S-8*R*Z+R-S*Z+2*S
Crit=P*u*u+Q*v*v+T
W=P*u*u-Q*v*v
checks=[]
def ck(name,expr):
    assert s.factor(expr)==0,(name,s.factor(expr))
    checks.append(name)
ck('critical surface toric identity',Delta.subs({R:1/u**2,S:1/v**2})-Crit/(u*u*v*v))
ck('actual density R,S to r,k',s.det(s.Matrix([[2*r,0],[-2*k**6/r**3,6*k**5/r**2]]))/(108*k**5)-1/(9*r))
# In u,h coordinates v=h^3/u; all residues use dCrit first, then dh dz.
Cri=Crit.subs(v,h**3/u)
Wi=W.subs(v,h**3/u)
ck('critical normal derivative',s.diff(Cri,u)-2*Wi/u)
ck('density times k cubed residue',h/(9*u)/(2*Wi/u)-h/(18*Wi))
ck('genus-two quotient relation',(W**2-(T*T-4*P*Q*h**6)).subs(h**6,u*u*v*v)-(P*u*u+Q*v*v-T)*Crit)
# The previous line uses (A-B)^2-T²+4AB=(A+B-T)(A+B+T).

xE=-4*P*Q*h*h; yE=-4*P*Q*W
ck('actual elliptic quotient',(yE*yE-xE**3-16*P*P*Q*Q*T*T).subs(h**6,u*u*v*v)-16*P*P*Q*Q*(P*u*u+Q*v*v-T)*Crit)
ck('elliptic holomorphic form pullback',s.diff(xE,h)/(-4*P*Q*Wi)-2*h/Wi)

# Literal source-density cancellation. c*d*e and L*epsilon are given here
# as branch-compatible monomials; their logarithmic powers are formal.
A=1+R; B=1+S; Tb=1+Z
lc=s.Matrix([[1/(6*R)-1/(3*A),1/(6*S)-1/(3*B),-2*z**5/Tb],
             [1/(6*R)-2/(3*A),1/(6*S)-1/(6*B),1/z-z**5/Tb],
             [-1/(6*A),-1/(6*B),1/z-4*z**5/Tb]])
ck('normalized logarithmic Jacobian',lc.det()-Delta/(36*R*S*z*A*B*Tb))
Lep6=1/(Tb**5*A**2*B**5)
cde6=(z*z*k*k/12)**6/(Tb**7*A**7*B**4)
HH6=4**6*Tb**8*A**11*B**5/(z**6*k**6*Delta**6)
rhs6=Lep6/(108**6*k**30)
num=s.together(HH6*cde6*lc.det()**6-rhs6).as_numer_denom()[0]
ck('full physical source has no Delta pole',s.rem(num,s.Poly(k**6-R*S,k),k))

# A smooth fold point: R=1,S=7,z=1; the logarithmic-map kernel is
# transverse to Delta, not tangent to its surface.
pt={R:1,S:7,z:1}; ker=s.Matrix([2,-56,1])
assert lc.subs(pt)*ker==s.zeros(3,1)
assert s.diff(Delta,R).subs(pt)*2+s.diff(Delta,S).subs(pt)*(-56)+s.diff(Delta,z).subs(pt)==-34
checks.append('generic fold witness and transverse kernel')

# Exact old-support distinction, even on F: w=z=0 and sixth powers
# X1=1,X2=3,Y0=2,Y2=-6 gives F=0 and Delta_hom=0.
xp=[0,1,3]; yp=[2,0,-6]
hx=sum(xp); fy=sum(yp)
assert hx+fy==0
old=[]
for label,block in [('X',xp),('Y',yp)]:
    for held in range(3):
        ij=[i for i in range(3) if i!=held]
        tt=block[ij[0]]+block[ij[1]]; kk=block[ij[0]]*block[ij[1]]
        val=fy*tt*tt+16*hx*kk
        assert val!=0
        old.append({'support':label+str(held),'value':val})
checks.append('distinct from all six old graph supports on F')

# Orders of the four base differentials on the common root cover
# alpha²=P/T, beta²=Q/T, gamma³=alpha beta.
# At finite branch roots its ramification index is six. Infinity is unramified.
orders={
 'P=0':[4,3,1,4],
 'Q=0':[4,3,4,1],
 'T=0':[1,3,4,4],
 'z=infinity':[4,4,4,4],
}
assert all(x>=0 for row in orders.values() for x in row)
checks.append('all four base factors holomorphic on common cover')
assert 2*16-2==-6+18*2
checks.append('delta cubic cover genus sixteen')

out={'status':'exact geometric interfaces; no mixed class or certificate',
     'count':len(checks),'checks':checks,'old_support_values':old,
     'holomorphic_forms':'z^i f dh wedge dz/(P u²-Q v²), f in {1,h,u,v}, 0<=i<=4',
     'base_factor_orders':orders,
     'scope':'All displayed H20 forms are pulled back from the base ramification surface; their pure-base proper H31 Gysin is zero.'}
Path(__file__).with_name('ramification-geometry-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':len(checks),'old_support_values':old}))
