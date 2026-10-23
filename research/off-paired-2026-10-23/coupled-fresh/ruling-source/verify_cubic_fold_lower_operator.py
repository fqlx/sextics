"""Exact full lower odd-principal map for the source-bound cubic lift.

No physical source is replaced by a leading approximation: this supplies
the exact triangular local jet map used to normalize the actual K/v.
Global interpolation and the retained regular target remain separate.
"""
import json
from collections import defaultdict
from pathlib import Path
import sympy as s

x,y=s.symbols('i J')
V=s.Function('V')(x,y)
r=s.Function('q3')(x,y)
t=s.Function('q5')(x,y)
p=s.diff(V,x);q=s.diff(V,y)
H=V-y*q
W=4*V+x*p+y*q
sigma=(-p**3+V**2*H*W)/8

def clean(F):return {k:s.expand(v)for k,v in F.items()if s.expand(v)!=0}
def add(*Fs):
    out=defaultdict(lambda:0)
    for F in Fs:
        for n,c in F.items():out[n]+=c
    return clean(out)
def scale(c,F):return clean({n:c*f for n,f in F.items()})
def deriv_base(F,variable):return clean({n:s.diff(c,variable)for n,c in F.items()})
def singular_deriv(F,coefficient,shift=-2):
    return clean({n+shift:n*coefficient*c for n,c in F.items()})
def A(F):return add(deriv_base(F,x),singular_deriv(F,-p/2))
def B(F):return add(deriv_base(F,y),singular_deriv(F,-q/2))
def Z(F):return add(singular_deriv(F,V/2),singular_deriv(F,s.Rational(1,2),0))
def D(F):return add(scale(6,Z(F)),scale(-2*x,A(F)),scale(-2*y,B(F)))
def mul_v(F):return add(scale(V,F),{n+2:c for n,c in F.items()})
def L3(F):
    inner=add(Z(F),scale(s.Rational(1,2),D(F)),scale(5,F))
    middle=Z(inner)
    outer=add(Z(middle),scale(y,B(middle)),scale(2,middle))
    return add(A(A(A(F))),mul_v(outer))

def lower(f):
    return s.Rational(3,8)*(
        (6*p*p-2*x*V*V*H)*s.diff(f,x)
        +2*y*V*V*(W-H)*s.diff(f,y)
        +(6*p*s.diff(V,x,2)+2*V*y*(q*W+V*s.diff(W,y))
          +3*V*V*W+22*V*V*H)*f)

checks={}
q3out=L3({3:r})
q5out=L3({5:t})
checks['q3_leading_coefficient']=s.expand(q3out.get(-3,0)+3*sigma*r)==0
checks['q3_complete_lower_coefficient']=s.expand(q3out.get(-1,0)-lower(r))==0
checks['q3_no_other_negative_powers']=set(n for n in q3out if n<0)=={-3,-1}
checks['q5_lower_coefficient']=s.expand(q5out.get(-1,0)-15*sigma*t)==0
checks['q5_no_other_negative_powers']=set(n for n in q5out if n<0)=={-1}
for n in (0,2,4,6):
    evenout=L3({n:s.Function('q'+str(n))(x,y)})
    checks['even_'+str(n)+'_regular']=all(k>=0 for k in evenout)

# The principal factor is exactly the full rational O3 symbol evaluated
# on ds=(dv−V_i di−V_J dJ)/(2s), not an unrelated new determinant.
zsym=V/2;asym=-p/2;bsym=-q/2;dsym=(6*V+2*x*p+2*y*q)/2
symbol=asym**3+V*(zsym+y*bsym)*zsym*(zsym+dsym/2)
checks['principal_symbol_match']=s.expand(symbol-sigma)==0

assert all(checks.values()),checks
out={
    'passed':True,'checks':checks,'certificate':False,
    'local_coordinate':'s^2=v-V(i,J), with V the actual moving fold value',
    'definitions':{'p':'V_i','q':'V_J','H':'V-J*V_J','W':'4V+i*V_i+J*V_J',
                   'sigma':'(-p^3+V^2*H*W)/8'},
    'lower_operator':'T=(3/8)*[(6p^2-2iV^2H)*partial_i+2JV^2(W-H)*partial_J+6pV_ii+2VJ(qW+VW_J)+3V^2W+22V^2H]',
    'jet_map':'L3Q=-3sigma*q3*s^(-3)+(T(q3)+15sigma*q5)*s^(-1)+regular, when q1=0',
    'scope':'Exact local source-current jet map. Actual source coefficient extraction, rational CRT interpolation, boundary preservation, and full regular/compact target must all be retained.'
}
Path(__file__).with_name('cubic-fold-lower-operator-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact moving-fold Laurent identities')
