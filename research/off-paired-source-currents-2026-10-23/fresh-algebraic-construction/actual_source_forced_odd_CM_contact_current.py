"""ONE source-forced absolute odd-CM contact current, with full remainder.

No fitted coefficients: its scalar is forced by the ENTIRE endpoint normal
packet.  The resulting actual curvature is checked rather than discarded.
"""
from pathlib import Path
import sympy as s,json,time
st=time.time()
u,w,q,z,p=s.symbols('u w q z p',nonzero=True)
eta=2*u+w**3-3*z*z/4
J=1+z**6+u*u+u*w**3-3*z*z*u/4
d=1+z**6-J
C=u*z/2+q/3
H=J+3*z*C/2
def red(v):
    nn,dd=s.fraction(s.cancel(v))
    dom=s.QQ.frac_field(u,w,z,p)
    mod=s.Poly(q*q-u*w,q,domain=dom)
    return s.factor(s.Poly(nn,q,domain=dom).rem(mod).as_expr()/dd)
def D(v,i):
    return s.diff(v,(u,w,z)[i])+(w if i==0 else u if i==1 else 0)*s.diff(v,q)/(2*q)
def grad(v):return s.Matrix([D(v,i) for i in range(3)])
gj=grad(J);gc=grad(C);gh=grad(H)
Omega=-(grad(u)/u-grad(d)/(2*d))/(3*q*eta)
contact=gj+s.Matrix([0,0,3*C/2])
# A2=(coefficient(dw dz),coefficient(dz du),coefficient(du dw));
# wedge A2 with df is the dot product with grad f.
raw=Omega.cross(contact)
mass=red(raw.dot(gc))
a0=w/(18*eta**2)
b0=z*w/(72*eta)+w*w/(216*q*eta)
forced=s.factor(s.cancel(-b0/mass))
K=s.Matrix([red(forced*v) for v in raw])
Path(__file__).with_name('actual_source_forced_odd_CM_contact_current_early.json').write_text(json.dumps({'forced_scalar':str(red(forced)),'current_vector':list(map(str,K)),'mass':str(mass)},indent=2)+'\n')
print('built whole current seconds',round(time.time()-st,3),flush=True)
checks={}
def ck(name,v):
    checks[name]=red(v)==0
    assert checks[name],(name,red(v))
ck('actual_odd_CM_absolute_lift',Omega[0]+(1/u-D(d,0)/(2*d))/(3*q*eta))
ck('forced_complete_C_normal',K.dot(gc)+b0)
ck('forced_complete_H_normal',K.dot(gh)+3*z*b0/2)
ck('forced_contact_constraint',K.dot(contact))
rho=w/(36*eta)
L=H+C*p;ff=L*L-4*p**6
original=-w*L/36
prior=red(D(rho,0)*ff-rho*L*(D(H,0)+p*D(C,0)))
ck('whole_original_to_Efree_prefix',original-prior-a0*ff-b0*L*(p+3*z/2))
print('whole normal matching checked seconds',round(time.time()-st,3),flush=True)
div=red(sum(D(K[i],i) for i in range(3)))
remaining=red(a0-div)
# Literal derivative of K2 wedge dp/Y: dK2*Y^-1 minus
# (K2^dH+p K2^dC)*(H+Cp)*Y^-3, with ALL coefficient motions.
literal=red(div*ff-L*(K.dot(gh)+p*K.dot(gc)))
target=red(a0*ff+b0*L*(p+3*z/2))
ck('WHOLE_current_plus_retained_packet',target-literal-remaining*ff)
pt={u:s.Integer(1),w:s.Integer(1),q:s.Integer(1),z:s.Integer(1)}
out={
 'status':'ONE_SOURCE_FORCED_ODD_CM_CONTACT_CURRENT_WITH_ENTIRE_RETAINED_PURE_HOL_REMAINDER',
 'checks':checks,'check_count':len(checks),
 'orientation':'vol_base=du wedge dw wedge dz; K vector denotes K0 dw dz+K1 dz du+K2 du dw.',
 'original_chart':'q²=u*w,J=1+z6+u²+uw³−3z²u/4,C=zu/2+q/3,H=J+3zC/2,etaB=2u+w³−3z²/4,d=1+z6−J.',
 'prior_literal_current':'Jcombined=w*dw wedge dz wedge dp/(36etaB*Y). This includes the Phi/CJ cochain; no E term or fixed-C Jacobian factor remains.',
 'WHOLE_prior_residual':'R=du dw dz dp*[a0/Y+b0*(H+Cp)*(p+3z/2)/Y³],a0=w/(18etaB²),b0=z*w/(72etaB)+w²/(216qetaB).',
 'absolute_CM_kernel':'OmegaT=OmegaOdd/lambda5=−[dlogu−(1/2)dlogd]/(3q etaB). This is the actual weighted three-rotation constant-CM Cauchy kernel; all dbase terms are retained.',
 'literal_current_constructor':'Acontact=dJ+(3/2)C dz, Kraw=OmegaT wedge Acontact. Set f=−b0/(Kraw wedge dC/vol_base), UNIQUE. JCM=K2 wedge dp/Y with K2=f*Kraw.',
 'forced_scalar':str(red(forced)),
 'current_vector':list(map(str,K)),
 'Kraw_dC_mass':str(mass),
 'whole_current_identity':'R=dJCM+(a0−divK)*du dw dz dp/Y. All endpoint-Y^-3 terms match identically, not only compact rows or relative residues.',
 'divK':str(div),'pure_hol_remaining':str(remaining),
 'actual_point':{'u':'1','w':'1','q':'1','z':'1','forced_scalar':str(red(forced).subs(pt)),
                 'a0':str(a0.subs(pt)),'divK':str(div.subs(pt)),'remaining':str(remaining.subs(pt))},
 'remaining_scope':'The explicit pure holomorphic endpoint theta0 packet must be served by the two q-even varying elliptic channels or another actual full current. The forced contact construction alone is not asserted to close, and no weights are varied.',
 'elapsed_seconds':round(time.time()-st,3)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'ONE forced full odd-CM contact current; remaining atpoint',remaining.subs(pt),round(time.time()-st,3),flush=True)
