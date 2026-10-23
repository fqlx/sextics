#!/usr/bin/env python3
"""Compact i primitive of Fresh's j primitive, with finite residues canceled."""
import json
from functools import lru_cache
from pathlib import Path
import sympy as s
a,y,x,i,j,v=s.symbols('a y x i j v')
@lru_cache(None)
def rw(A,B,X):
 if A and B:
  z=min(A,B);return rw(A-z,B-z,X+3*z)
 if A>=2:return s.expand(-rw(A-2,B+2,X)/v-i*rw(A-2,B,X+2)-j*rw(A-1,B,X+1)-rw(A-2,B,X+1)-rw(A-2,B,X))
 if B>=3:return s.expand(-v*rw(A+1,B-3,X+3)-v*i*rw(A,B-2,X+2)-v*j*rw(A,B-3,X+4)-v*rw(A,B-2,X+1)-v*rw(A,B-2,X))
 return a**A*y**B*x**X

def red(f):return s.expand(sum(z*rw(*k) for k,z in s.Poly(s.expand(f),a,y,x).terms()))
J=red(2*v*a*a+j*v*a*x-2*y*y)
da=red(-a*v*(2*i*x+j*a+1)-6*y*x*x)
dy=red(v*(y*(2*i*x+j*a+1)+3*x*x*(2*a+j*x)))
def dd(f):return red(s.diff(f,x)*J+s.diff(f,a)*da+s.diff(f,y)*dy)
co={4:s.Rational(1,8),3:s.Rational(1,24),2:i/8-s.Rational(1,24),1:s.Rational(1,24)-i/6}
F=sum(z*y*y/x**k for k,z in co.items())
cleared=red(-y*y*J/2+j*y*x**4*J/2-sum(z*(x**(5-k)*dd(y*y)-k*x**(4-k)*y*y*J) for k,z in co.items()))
assert all(k[2]>=5 for k,z in s.Poly(cleared,a,y,x).terms())
P=s.cancel(cleared/x**5)
rows=[(A,B,X) for A,B in [(0,0),(1,0),(0,1),(0,2)] for X in range((8-3*A-3*B)//2+1)]
mon=lambda w:a**w[0]*y**w[1]*x**w[2]
vec=lambda f:s.Matrix([s.Poly(red(f),a,y,x).coeff_monomial(mon(w)) for w in rows])
basis=[1,x,x*x,x**3,x**4,a,a*x,y,y*x];func=[x,x*x,a,y]
M=s.Matrix.hstack(*(vec(z) for z in [dd(z) for z in func]+[v*z for z in basis]));sol=M.inv()*vec(P)
coeff=[s.factor(z) for z in sol[4:]];fexact=sum(z*q for z,q in zip(func,sol[:4]))
assert red(P-dd(fexact)-sum(v*z*q for z,q in zip(basis,coeff)))==0
# Raw to compact vector, omega omitted only after exact residue cancellation.
cp=i-j*j/4;r=cp*(cp-j*j)/8
omega=s.factor(coeff[2]+v*r*coeff[4]-j*coeff[6]/2);assert omega==0,omega
C=[coeff[k] for k in [0,1,3,4,5,6,7,8]]
# Direct literal derivative before reduction: Vi_raw=-x/(2a²).
aj=-v*a*a*x/(2*v*a*a+j*v*a*x-2*x**6/a**2)
ai=-v*a*x*x/(2*v*a*a+j*v*a*x-2*x**6/a**2)
checks={'literal_mixed_i_derivative':s.cancel(s.diff(-x/(2*a*a),a)*ai+v*x**3/(a*a*(2*v*a*a+j*v*a*x-2*x**6/a**2)))==0,'finite_residue_cancellation':True,'all_finite_poles_removed_by_F':True,'generic_polynomial_reduction':True,'zero_infinity_residue_component':omega==0}
# Verify full compact derivative against independently built Gamma_i and U.
base=Path(__file__).parent.parent/'ruling-source/full-base-connection'
gi=json.loads((base/'rank8-ij-connections-results.json').read_text());gu=json.loads((base/'j-source-primitive-results.json').read_text())
D=s.sympify(gi['common_denominator']);GN=s.Matrix([[s.sympify(z) for z in ar] for ar in gi['Gamma_numerators']['i']])
U=s.Matrix([v*(5*j*j-12*i)/48,v*(5*j*j-12*i)/48,-1,2,-5*j*v/24,j*v*(15*j*j-52*i)/96,0,-j/2]);CV=s.Matrix(C)
check=GN*CV+D*CV.diff(i)-D*(U+s.Matrix([0,0,0,0,0,0,0,j/2]))
checks['all_eight_generic_mixed_connection_identities']=all(s.expand(z)==0 for z in check)
assert all(checks.values()),checks
out=Path(__file__).with_name('mixed-i-primitive-results.json');out.write_text(json.dumps({'status':'Explicit source-directed compact mixed current; density derivatives remain and no certificate claimed','raw_i_primitive_of_U1':'-x/(2a²)dx=-y²dx/(2x⁵)','raw_finite_residue':'-j*r/2 at Pa, r²=-v; zero infinity residue','compact_moment':'Vi=raw_i_primitive+j*zeta_hat/2','finite_pole_primitive_F':str(F),'remaining_exact_polynomial_primitive':str(s.factor(fexact)),'compact_basis':['1','x','x³','x⁴-v*r*x²','a','a*x+j*x²/2','y','y*x'],'compact_vector':[str(z) for z in C],'mixed_identity':'nabla_i Vi=U1+(j/2)nu_bq','checks':checks,'certificate':False},indent=2)+'\n')
print('compactvector',C);print('saved',out)
