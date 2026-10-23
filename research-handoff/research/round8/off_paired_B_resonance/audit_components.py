"""Exact generic affine B=0 place audit for the charged cyclic scalar route.

No restriction to a worked invariant level is made here.
"""
from pathlib import Path
import json,time
import sympy as sp

HERE=Path(__file__).parent
START=time.monotonic()
eta,V,s=sp.symbols('eta V s')
vs=(eta,V,s)
c=sp.Rational(5,7)
obj=json.loads(Path('/workspace/research/round8/cyclic_companion/gist/results/original_scalar_input.json').read_text())
Y=[sp.sympify(a)for a in obj['contracted_boundary_reduction']['Y_components']]
Delta=sp.sympify(obj['contracted_boundary_reduction']['Delta0'])
T=sp.sympify(obj['T'])
R=sp.sympify(obj['contracted_boundary_reduction']['Rnum0'])
E=eta+1
hh=eta*V**2+1
k=1+V**6+s*s
q=3*k-c*V**2*s*E*hh
M=3*k/q
rx=(3*c*eta*k-c*c*V*s*hh*hh)/(E*q)
xx=3*V**3*s*E**3/q
L=(27*k*k*(1+eta**6*s*s)-9*c*c*eta*V**2*s*k*hh+2*c**3*V**3*s*s*hh**3)/(3*q*q)
H=hh/(V*E*E)
D=c*(3+c*xx*H)
N=3*rx+c*c*xx*H*H
A=D-N
B=27*c*c*L-3*D*D+9*c**3*xx*rx*H+c**5*xx*xx*H**3
assert sp.cancel(D-9*c*k/q)==0
assert sp.cancel(N-9*c*eta*k/(E*q))==0
assert sp.cancel(A-9*c*k/(E*q))==0
assert sp.cancel(B-243*c*c*eta**6*s*s*k*k/(q*q))==0
g=sp.cancel(A/(D*N))
assert sp.cancel(g-q/(9*c*eta*k))==0

def kord(f):
    p=sp.Poly(f,s,domain=sp.QQ.poly_ring(eta,V))
    mod=sp.Poly(k,s,domain=p.domain)
    n=0
    while not p.is_zero:
        quotient,remainder=p.div(mod)
        if not remainder.is_zero:return n,remainder.as_expr()
        n+=1
        p=quotient
    return 100,sp.Integer(0)

Yk=6*V**5*Y[1]+2*s*Y[2]
assert kord(Yk)[0]==1
assert min(m[2]for m,a in sp.Poly(Y[2],vs).terms())==1
assert sp.Poly(Y[0].subs(eta,0),V,s)!=0
for f in [q,Delta,T,R]:
    assert kord(f)[0]==0
    assert f.subs(eta,0)!=0
    assert f.subs(s,0)!=0

q0=3*(1+V**6)
d0=sp.factor(Delta.subs(s,0))
vel=[sp.factor(f.subs(s,0)/(q0*d0))for f in Y[:2]]
mu=sp.factor(sp.diff(Y[2],s).subs(s,0)/(q0*d0))
chi=V**3*E**3/(1+V**6)
assert sp.factor(mu+27+sum(vel[i]*sp.diff(chi,z)/chi for i,z in enumerate([eta,V])))==0
rhs_s=sp.factor(-sp.Rational(3,5)*T.subs(s,0)*R.subs(s,0)/d0**3)

report={
 'field':'QQ(eta,V,s), c=5/7; no invariant-level specialization',
 'exact_B_factorization':'B=243*c^2*eta^6*s^2*k^2/q^2',
 'exact_gauge':'g=A/(D*N)=q/(9*c*eta*k)',
 'verified_compact_substitution':True,
 'components':[
  {'place':'eta=0','ord_B':6,'ord_g':-1,'delta':'transverse at a generic point','ord_original_source':0,'ord_gauged_source':1,'charge_pole':'reduced charge has integer residue 1; original charge is regular, so this is a removable rational-gauge pole'},
  {'place':'s=0','ord_B':2,'ord_g':0,'delta':'invariant: delta(s)=s*mu, mu generically nonzero','ord_original_source':-1,'ord_gauged_source':-1,'charge_pole':'none: delta(log B) is regular despite ord(B)=2'},
  {'place':'k=0','ord_B':2,'ord_g':-1,'delta':'invariant: k exactly divides Y(k) once','ord_original_source':1,'ord_gauged_source':2,'charge_pole':'none: delta(log k) is regular'},
 ],
 's_boundary':{'delta_eta':str(vel[0]),'delta_V':str(vel[1]),'delta_s_over_s':str(mu),'source_times_s':str(rhs_s),'x_over_s':str(chi),'delta_log_x_limit':-27,'A0':27,'C0':162,'leading_original_operator_on_u=w/s':'(delta0-4*mu/3)^2-27*(delta0-4*mu/3)+162'},
 'scope':'At ordinary generic affine points, no transverse fractional-exponent resonance follows from B=0. The eta pole is gauge-removable; at invariant s,k divisors a flow-box gives local analytic meromorphic solutions with the stated pole order. This is not rational solvability over the residue function field, a fixed-level normalization, or a global scalar/certificate result. Exceptional places over intersections and infinity are not classified.',
 'seconds':round(time.monotonic()-START,3),
}
(HERE/'component_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
