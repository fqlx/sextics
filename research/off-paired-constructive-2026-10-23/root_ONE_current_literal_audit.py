"""Independent literal exterior derivative of complete three-piece candidate.
No compact reduction, quotient by exact fiber terms, or dropped base normals.
"""
from pathlib import Path
import sympy as s,json
H,C,p,Z,k,l,kh,kl,ll=s.symbols('H C p Z vH vC vHH vHC vCC')
L=H+C*p;ff=L*L-4*p**6
cl=lambda f:s.factor(s.cancel(f))
def deriv(f,i):
    x=[H,C,p][i]; zpart=[L/Z,p*L/Z,(C*L-12*p**5)/Z][i]
    out=s.diff(f,x)+s.diff(f,Z)*zpart
    if i==0:out+=s.diff(f,k)*kh+s.diff(f,l)*kl
    if i==1:out+=s.diff(f,k)*kl+s.diff(f,l)*ll
    return cl(out)
def wedge(a,b):return [cl(a[0]*b[1]-a[1]*b[0]),cl(a[0]*b[2]-a[2]*b[0]),cl(a[1]*b[2]-a[2]*b[1])]
def d1(a):return [cl(deriv(a[1],0)-deriv(a[0],1)),cl(deriv(a[2],0)-deriv(a[0],2)),cl(deriv(a[2],1)-deriv(a[1],2))]
def cross12(a,b):return cl(a[0]*b[2]-a[1]*b[1]+a[2]*b[0])
def cross21(a,b):return cl(a[0]*b[2]-a[1]*b[1]+a[2]*b[0])
def red(f):
    n,de=s.fraction(s.cancel(f));n=s.rem(s.Poly(n,Z),s.Poly(Z*Z-ff,Z)).as_expr();return cl(n/de)
Ev=3*H*k+2*C*l;m=l/(216*Ev);a=k/(432*Ev)
phi=C*C*k*k/(432*Ev)-C*C*k/(1296*H)
dv=[k,l,0];xi=[1/Z,p/Z,-(3*H+2*C*p)/(p*Z)]
lam=[cl(p*x) for x in xi];tau=[cl(p*p*x/C) for x in xi]
A=[a*k-k/(1296*H),a*l,0];B=[p*0,p/(2*Z),-C/Z]
mdv=[m*k,m*l,0];dphi=[deriv(phi,i) for i in range(3)]
# d(jcontact)=d(mdv)^B -mdv^dB; d(jlambda)=dA^lam-A^dlam;
# d(jtau)=-dphi^dtau, using d²phi=0 exactly.
djc=cross21(d1(mdv),B)-cross12(mdv,d1(B))
djl=cross21(d1(A),lam)-cross12(A,d1(lam))
djt=-cross12(dphi,d1(tau))
checks={
 'absolute_log_Xi_is_closed':all(red(x)==0 for x in d1(xi)),
 'literal_complete_current_source_remainder':red(-(djc+djl+djt)-kl/(432*Z)+l*L/(432*Z**3))==0,
}
jc=wedge(mdv,B);jl=wedge(A,lam);dtau=d1(tau)
basic=[0,0,-l/(432*Z)]
checks['entire_prefix_is_literal_elementary_IBP_plus_exact_current']=all(red(jc[i]+jl[i]-basic[i]-phi*dtau[i])==0 for i in range(3))
assert all(checks.values()),checks
out={'status':'PASS_FULL_LITERAL_EXTERIOR_DERIVATIVE_ONE_THREE_PIECE_CURRENT_NOT_CERTIFICATE','checks':checks,'check_count':len(checks),'identity':'beta_U=d(Jcontact+Jlambda+Jtau)−eta*dH*dC*vHC*theta0/432','verification':'Complete rational exterior derivative in H,C,p,Z with Z²=(H+Cp)²−4p6; vH,vC,vHH,vHC,vCC treated as compatible arbitrary jets. Every absolute endpoint base leg retained. No compact/fiber-exact reduction used.','remaining':'vHC generically nonzero. This verifies a partial current, not a certificate.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
