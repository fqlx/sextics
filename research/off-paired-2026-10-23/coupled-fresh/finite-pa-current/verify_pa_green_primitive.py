#!/usr/bin/env python3
"""Exact source-carrying finite-Pa current from existing Green identities.

The scalar K identity is the audited actual-source construction. This file
checks its complete residue reconstruction and compact-only remainder.
It does not prove the compact remainder exact.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

c,d,e,q,b=s.symbols('c d e q b')
xs=(c,d,e)
avec=s.Matrix([-c/3,-2*d/3,-e/6])
bvec=s.Matrix([-c/3,-d/6,-e/6])
tvec=s.Matrix([-c/3,-d/6,-2*e/3])
zvec=-bvec
E=s.Matrix([0,0,1]); C=s.Matrix([1,0,0]); DD=s.Matrix([0,1,0])

def act(v,f):return sum(vv*s.diff(f,x) for vv,x in zip(v,xs))
def div(v):return sum(s.diff(vv,x) for vv,x in zip(v,xs))
def aa(f):return act(avec,f)
def bb(f):return act(bvec,f)
def tt(f):return act(tvec,f)
def zz(f):return act(zvec,f)

def pe(f):return s.diff(f,e,2)-tt(s.diff(f,c))-s.diff(f,c)/6
def pd(f):return s.diff(f,d,2)-aa(s.diff(f,c))+s.diff(f,c)/3
def p3(f):return aa(bb(tt(f)+f/2)-(tt(f)+f/2)/2)-s.diff(f,c,3)
def pes(f):return s.diff(f,e,2)-s.diff(tt(f)-4*f/3,c)
def pds(f):return s.diff(f,d,2)-s.diff(aa(f)-5*f/6,c)
def p3s(f):
    u=tt(f)-5*f/3
    v=bb(u)-u/6
    return s.diff(f,c,3)-aa(v)+7*v/6

checks=[]
def check(name,f):
    f=s.expand(f)
    assert f==0,(name,f)
    checks.append(name)

H=s.Function('H')(c,d,e)
f=s.Function('f')(c,d,e)
g=s.Function('g')(c,d,e)
h=s.Function('h')(c,d,e)
K=s.Function('K')(c,d,e)
chi=s.Function('chi')(c,d,e)

one=s.Integer(1)
check('PE annihilates constant residue',pe(one))
check('PD annihilates constant residue',pd(one))
check('P3 annihilates constant residue',p3(one))

# Complete Green vectors specialized at chi=1, including cubic Euler terms.
BE=-s.diff(f,e)*E+(tt(f)-4*f/3)*C
BD=-s.diff(g,d)*DD+(aa(g)-5*g/6)*C
Ast=-aa(h)+7*h/6
BstAst=-bb(Ast)+Ast/6
B3=-h*avec/4+Ast*bvec/2+BstAst*tvec-s.diff(h,c,2)*C
check('finite PE Green identity',div(BE)+pes(f))
check('finite PD Green identity',div(BD)+pds(g))
check('finite P3 Green identity',div(B3)+p3s(h))

V=s.diff(H,e)*E+BE+BD+B3
source=s.diff(H,e,2)-pes(f)-pds(g)-p3s(h)
check('full finite source divergence',div(V)-source)

M=e**(-7)*K
R=zz(K)-K
check('weighted Z divergence',div(M*zvec)-e**(-7)*R-M/2)
W=V-M*zvec
# For actual data source=e^-7 R, this proves div W=-M/2.
check('actual Pa primitive implication',div(W)+M/2-(source-e**(-7)*R))

# Product rule before imposing the source identity. Once div W=-M/2,
# M(B0-1/2)chi = div(W chi)-V(chi).
check('full compact-only source identity',
      M*(bb(chi)-chi/2)-div(W*chi)+act(V,chi)
      -(e**(-7)*R-source)*chi)

# The three remaining derivatives are literal polynomial/J differentials.
P=b**4+(c*q*q+e*q+1)*b*b+d*q**4*b+q**6
Pb=s.diff(P,b)
a=q**3/b
J=2*a*a+d*a*q-2*b*b
def implicit(f,x):return s.diff(f,x)-s.diff(P,x)*s.diff(f,b)/Pb
for x,wanted in [(c,b*q/J),(d,q**3/J),(e,b/J)]:
    diff=s.cancel(implicit(b/q,x)-wanted)
    num=diff.as_numer_denom()[0]
    assert s.rem(num,P,b)==0,(x,num)
    checks.append('literal compact derivative '+str(x))

# Orientation and physical density: M mu = -K/3 di dj dh.
hbase=s.symbols('hbase')
check('Pa density orientation',(-M/s.Integer(2)).subs(K,1)*(-e**7/s.Integer(3))-s.Rational(1,6))

root=Path(__file__).resolve().parents[1]
binding=root/'genus4-gm-independent/corrected-rational-source-binding.json'
result={
 'status':'Actual finite Pa residue has an explicit full-base primitive; compact serving remains open',
 'source_binding_sha256':hashlib.sha256(binding.read_bytes()).hexdigest(),
 'actual_source_record':'actual Ssrc=(D-6)(D-5)hsrc, not undifferentiated hsrc residue',
 'normalized_potentials':{'f':'e^-5 F','g':'e^-5 G','h':'e^-1 Hpot','H':'Hsrc=e^-5 hsrc','M':'e^-7 K'},
 'vector_V':'H_e partial_e+B_PE(f,1)+B_PD(g,1)+B_P3(h,1)',
 'vector_W':'V-M Z, Z=-B0',
 'divergence':'div W=-M/2 using the audited actual scalar identity',
 'Pa_primitive':'plus/minus sqrt(-1) * contraction(W,dc wedge dd wedge de)',
 'Pa_source':'plus/minus sqrt(-1) K dh wedge di wedge dj/6',
 'compact_remainder':'-V_c b*q dq/J - V_d q^3 dq/J - V_e b dq/J',
 'warning':'This is a residue current and an equivalent compact source. It is not a new compact exactness result; it reduces to first source integration by parts if all three potentials vanish. Original source has the opposite overall sign.',
 'checks':checks,'count':len(checks),'certificate':False}
out=Path(__file__).with_name('pa-green-primitive-results.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'count':len(checks),'pass':True,'output':str(out)}))
