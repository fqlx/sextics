#!/usr/bin/env python3
"""Exact trace-zero algebraic connection for the actual quartic K source.

The source multiplier remains H=K/v, with the full physical w dependence.
An auxiliary polynomial-in-f integration formula is checked separately;
the actual H has NOT been replaced by such a polynomial.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

HERE=Path(__file__).resolve().parent
a,p,q,r,l=s.symbols('a p q r l')
FF=s.QQ.frac_field(p,q,r,l)
P=s.Poly(a**4+p*a**3+q*a*a+r,a,domain=FF)
Pa=P.diff()

def red(x):
    num,den=s.fraction(s.cancel(x))
    pn=s.Poly(num,a,domain=FF)
    pd=s.Poly(den,a,domain=FF)
    return (pn*s.invert(pd,P)).rem(P).as_expr()

def dr(x):
    return red(s.diff(x,r)-s.diff(x,a)*s.invert(Pa,P).as_expr())

basis=[a+p/4,a*a-(p*p-2*q)/4,a**3+(p**3-3*p*q)/4]
def coeffs(x):
    rr=red(x)
    pp=s.Poly(rr,a)
    vv=s.Matrix([pp.coeff_monomial(a**k) for k in (1,2,3)])
    assert red(rr-sum(c*b for c,b in zip(vv,basis)))==0
    return vv.applyfunc(s.factor)

checks={}
def check(name,x):
    assert red(x)==0,(name,x)
    checks[name]=True

gamma=s.Matrix.hstack(*(coeffs(dr(b))for b in basis))
for k,b in enumerate(basis):
    check('connection_column_'+str(k),dr(b)-sum(gamma[t,k]*basis[t]for t in range(3)))

# Trace-zero checks do not require a splitting field.
tr=[4,-p,p*p-2*q,-p**3+3*p*q]
def trace(x):
    pp=s.Poly(red(x),a)
    return s.factor(sum(pp.coeff_monomial(a**k)*tr[k]for k in range(4)))
for k,b in enumerate(basis):
    assert trace(b)==0
    checks['traceless_basis_'+str(k)]=True

u=red(1/a)
uv=coeffs(u)
assert uv==s.Matrix([-q/r,-p/r,-1/r])
checks['inverse_a_exact_vector']=True
duv=(uv.diff(r)+gamma*uv).applyfunc(s.factor)
check('inverse_a_derivative',sum(duv[t]*basis[t]for t in range(3))-1/(a*a*Pa.as_expr()))
assert trace(dr(u))==0
checks['source_trace_zero']=True

# Source from the full kernel, r=f(w)*l^6, H=K/v=K*f.
# S=-l^2 H r_w (du/dr)/6; p=j*l, q=i*l^2+l+1.
kernel=s.symbols('K')
fw=s.symbols('f_w')
source=kernel*fw*l*l*(a*a+p*a+q)/(6*Pa.as_expr())
H=kernel*r/l**6
check('actual_source_single_derivative',(a*a+p*a+q)/Pa.as_expr()+r*dr(u))

# Constructive polynomial-density serving, ONLY when the actual H has that
# additional proven form. It is not assumed in the current construction.
f_of_a=-a*a*(a*a+p*a+q)/l**6
polynomial_primitives=[]
for n in range(5):
    integrand=s.cancel(l*l*f_of_a**n/(6*a*a))
    primitive=s.integrate(s.expand(integrand),a)
    assert not primitive.has(s.log)
    assert s.cancel(s.diff(primitive,a)-integrand)==0
    # Its r derivative on the quartic gives the n-th source, H=(r/l^6)^n.
    check('polynomial_f_monomial_'+str(n),dr(primitive)+l*l*(r/l**6)**n*dr(u)/6)
    polynomial_primitives.append(str(s.factor(primitive)))

disc=s.factor(s.discriminant(P.as_expr(),a))
assert s.expand(disc-r*(256*r*r+(144*p*p*q-128*q*q-27*p**4)*r+16*q**4-4*p*p*q**3))==0
checks['quartic_discriminant']=True

# Full direct fold current, with all unknown regular jets retained. Here
# t=w-c and qinv*f''=1 modulo the simple critical polynomial.
tt=s.symbols('t')
hm3,hm1,hzero,f2,f3,f4,uf0,uf1,qi1,qi2=s.symbols('hm3 hm1 h0 f2 f3 f4 uf0 uf1 qi1 qi2')
hm2=-hm3*f3/(2*f2)
hh=hm3/tt**3+hm2/tt**2+hm1/tt+hzero
ffp=f2*tt+f3*tt**2/2+f4*tt**3/6
uf=uf0+uf1*(f2*tt**2/2+f3*tt**3/6)
qi=1/f2+qi1*tt+qi2*tt**2
ss=-l*l*hh*ffp*uf/6
bf=l*l*hh*ffp**2*qi*uf/6
assert s.expand(ss).coeff(tt,-1)==0
checks['actual_fold_zero_residue_jet']=True
assert s.expand(ss).coeff(tt,-2)==-l*l*hm3*f2*uf0/6
checks['actual_fold_double_principal']=True
assert s.expand(bf).coeff(tt,-1)==l*l*hm3*f2*uf0/6
checks['compressed_fold_current_principal']=True
reg=s.expand(ss-s.diff(bf,tt))
for deg in (-3,-2,-1):
    assert reg.coeff(tt,deg)==0
checks['compressed_fold_residual_regular']=True

# Full cubic moment properization need not preserve the original fold
# order. Its generic Q_s term creates H~s^-5. Audit the corrected order and
# all local source primitives without discarding either principal level.
sig,qone=s.symbols('sigma3 q1')
lead=lambda x:s.diff(x,tt)/tt
assert s.expand(sig*lead(lead(lead(qone*tt))))==3*sig*qone/tt**5
checks['cubic_properization_can_raise_H_to_order_five']=True
hm5,u2,u4,u6=s.symbols('hm5 u2 u4 u6')
hh5=hm5/tt**5+hm3/tt**3+hm1/tt
uu=u2*tt**2+u4*tt**4+u6*tt**6
ss5=s.expand(-l*l*hh5*s.diff(uu,tt)/6)
assert ss5.coeff(tt,-3)==0 and ss5.coeff(tt,-1)==0
checks['properized_source_zero_residue_and_parity']=True
bb5=l*l*hm5*u2/(9*tt**3)+l*l*(hm3*u2+2*hm5*u4)/(3*tt)
rr5=s.expand(ss5-s.diff(bb5,tt))
assert all(rr5.coeff(tt,k)==0 for k in range(-4,0))
checks['properized_two_level_local_current']=True

binding=(HERE.parent/'genus4-gm-independent/corrected-rational-source-binding.json')
out={
 'status':'Exact source-preserving rank-three algebraic w connection; primitive remains open',
 'source_sha256':hashlib.sha256(binding.read_bytes()).hexdigest(),
 'curve':'P=a^4+p*a^3+q*a^2+r; p=j*l,q=i*l^2+l+1,r=f(w)*l^6,f=1/v(i,j^2,w)',
 'basis':[str(b)for b in basis],
 'convention':'columns satisfy d_r basis_j=sum_i Gamma_ij basis_i; d_w=(f_w*l^6)d_r',
 'matrix_dr':[[str(gamma[x,y])for y in range(3)]for x in range(3)],
 'inverse_a_vector':[str(t)for t in uv],
 'inverse_a_derivative_vector':[str(t)for t in duv],
 'actual_source_vector':'-l^2*H*f_w*l^6/6 * inverse_a_derivative_vector; H=K/v=PN+Ctot, full actual source retained',
 'source_one_column_identity':'S=-l^2*H/6*d_w(1/a)',
 'integration_by_parts':'S=d_w[-l^2*H/(6a)]+l^2*H_w/(6a); last term retained',
 'discriminant':str(disc),
 'actual_fold_current':{
   'critical_polynomial':'C is the saturated squarefree numerator of f_w; fixed-boundary factors omitted',
   'scalar_inverse':'qinv*f_ww=1 mod C, qinv polynomial remainder modulo C over the base field',
   'primitive':'Bfold=+l^2*H*f_w^2*qinv*(d_f(1/a))/6',
   'retained_source':'Sreg=-l^2*H*f_w*d_f(1/a)/6 - d_w(Bfold)',
   'regularity':'Sreg has no pole at any simple physical fold where the quartic fiber is smooth',
   'scope':'One-level formula applies to original H foldorder3. Full cubic moment properization can raise H toorder5; then use the m=4,3,2 Hermite recursion. Boundary and infinity sources retained.'},
 'properized_fold_recursion':{
   'H_fold_powers':[-5,-3,-1],
   'source_max_pole_order':4,
   'steps':[4,3,2],
   'numerator_formula':'t=-(C^m S mod C)*inverse((m-1)Cprime mod C) mod C',
   'current':'Y_m=t/C^(m-1); subtract (partial_w+Gamma_w)Y_m',
   'final_simple_remainder':'zero by actual Morse parity',
   'scope':'Complete finite fold pole reduction, not a full source primitive'},
 'polynomial_f_serving':{
   'scope':'Only if H=K/v is PROVED polynomial in f; actual H is not assumed so',
   'all_degree_formula':'B=l^2/6*(-h0/a+sum_{n>=1} hn*(-1)^n/l^(6n)*integral[a^(2n-2)*(a^2+p*a+q)^n da]); source S=d_w B; four-form current is -B*dl*di*dj',
   'checked_monomial_primitives_n_0_through_4':polynomial_primitives},
 'checks':checks,'count':len(checks),
 'limitations':'No rational w solution for full actual H is claimed. The physical cover and trace-zero quartic sector are retained.'}
path=HERE/'quartic-w-connection-results.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'output':str(path)}))

if __name__=='__main__':
    pass
