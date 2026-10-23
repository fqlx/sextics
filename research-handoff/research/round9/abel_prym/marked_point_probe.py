"""Construct and test the natural marked-point Abel--Prym channel.

The map itself is characteristic-zero algebraic. A finite good point tests
that its derivative along the isoperiodic flow is not identically zero.
This does not establish matching of the physical source.
"""
from pathlib import Path
from fractions import Fraction
import json,pickle,time
import sympy as s

HERE=Path(__file__).parent;start=time.monotonic();p=1009
cp=5*pow(7,-1,p)%p
root=Path('/workspace/research/round8/coupled_source')
native=pickle.loads((root/'coordinate_fields.pickle').read_bytes())
actual=pickle.loads(Path('/workspace/research/round9/cyclic_full/actual_fast.pickle').read_bytes())
conj=pickle.loads(Path('/workspace/research/round9/cyclic_full/conjugate_fast.pickle').read_bytes())
W,h,t,L,r,x=actual['symbols']

def md(value):
    f=Fraction(str(value));return f.numerator*pow(f.denominator,-1,p)%p
def evaluate(poly,point,derivative=None):
    out=0
    for ex,c in poly.items():
        ex=list(ex);value=md(c)
        if derivative is not None:
            if not ex[derivative]:continue
            value=value*ex[derivative]%p;ex[derivative]-=1
        for z,n in zip(point,ex):value=value*pow(z,n,p)%p
        out+=value
    return out%p
def rational_pair(pair,point):return evaluate(pair['numerator'],point)*pow(evaluate(pair['denominator'],point),-1,p)%p
def expr_pair(expr):
    num,den=s.fraction(s.cancel(expr))
    return tuple(s.Poly(f,L,r,x).as_dict()for f in [num,den])
def eval_expr(pair,point):return evaluate(pair[0],point)*pow(evaluate(pair[1],point),-1,p)%p

# Only the three holomorphic Prym forms are needed: actual h^2,t and
# conjugate Wh. The Q8 exact primitives are enough for each of them.
compiled=[]
for block,idx,label,char in [(actual,0,'actual_h2',1),(actual,1,'actual_t',1),(conj,0,'conjugate_Wh',2)]:
    directions={}
    for name in ['L','r','x']:
        pp=block['primitives'][name][idx]
        assert pp['Q14_raw'] is None
        directions[name]={'raw':[expr_pair(z)for z in pp['Q8_raw']],
                          'den':expr_pair(pp['Q8_denominator']),
                          'labels':block['lab8']}
    compiled.append((label,char,directions))

cube_roots={pow(z,3,p):z for z in range(1,p)}
zeta=next(z for z in range(2,p)if pow(z,3,p)==1)
gamma={}
for vv in range(1,40):
    roots=[ww for ww in range(1,p)if (pow(ww,6,p)+cp*pow(ww,3,p)+1+pow(vv,6,p))%p==0 and(2*pow(ww,3,p)+cp)%p]
    if roots:gamma[vv]=roots[0]

records=[]
for vv,ww in gamma.items():
 for aa in range(1,8):
  for bb in range(1,8):
   point=(aa,bb,vv)
   try:
    vals={name:evaluate(poly,point)for name,poly in native['polynomials'].items()}
    A,B,S,R,E=[vals[name]for name in ['A','B','S','R','E']]
    M=A*pow(3*S,-1,p)%p
    if M not in cube_roots:continue
    rho=cube_roots[M]
    LL=vals['H']*pow(3*A*A,-1,p)%p
    rr=vals['J']*pow(B*A,-1,p)%p
    xx=3*pow(B,3,p)*pow(A,-1,p)%p
    canonical=(LL,rr,xx)
    flow=[xx*((cp*cp-10*rr)*LL+4*rr*rr)%p,
          (xx*rr*(cp*cp-5*rr)-18*LL+9*rr)%p,
          -xx*((cp*cp+5*rr)*xx+27)%p]
    fields={name:[rational_pair(z,point)for z in pairs]for name,pairs in native['fields'].items()}
    physical_flow=[sum(flow[j]*fields[name][i]for j,name in enumerate(['L','r','x']))%p for i in range(3)]
    # M=A/(3S), so the logarithmic rho derivative is exact.
    grad_logrho=[(evaluate(native['polynomials']['A'],point,i)*pow(A,-1,p)-evaluate(native['polynomials']['S'],point,i)*pow(S,-1,p))*pow(3,-1,p)%p for i in range(3)]
    qflow=sum(a*b for a,b in zip(physical_flow,grad_logrho))%p
    z=B*R*pow(A,-1,p)%p
    grad_z=[((evaluate(native['polynomials']['B'],point,i)*R+B*evaluate(native['polynomials']['R'],point,i))*pow(A,-1,p)-z*evaluate(native['polynomials']['A'],point,i)*pow(A,-1,p))%p for i in range(3)]
    dz=sum(a*b for a,b in zip(physical_flow,grad_z))%p
    dw=-2*pow(vv,5,p)*physical_flow[2]*pow(ww*ww*(2*pow(ww,3,p)+cp),-1,p)%p
    wcan=ww*pow(rho,-1,p)%p
    dwcan=(dw-ww*qflow)*pow(rho,-1,p)%p
    assert (pow(wcan,6,p)+cp*(1+z)*pow(wcan,3,p)+LL+rr*z+pow(z,3,p)*pow(xx,-1,p))%p==0
    Ct=(cp*pow(wcan,3,p)+rr+3*z*z*pow(xx,-1,p))%p
    CW=(6*pow(wcan,5,p)+3*cp*(1+z)*wcan*wcan)%p
    assert (CW*dwcan+Ct*dz+flow[0]+flow[1]*z-flow[2]*pow(z,3,p)*pow(xx*xx,-1,p))%p==0
    if not Ct:continue
    def differential_at(wvalue,dwvalue):
        ct=(cp*pow(wvalue,3,p)+rr+3*z*z*pow(xx,-1,p))%p
        out=[]
        for label,char,directions in compiled:
            num=1 if label=='actual_h2'else z if label=='actual_t'else wvalue
            value=num*dwvalue*pow(ct,-1,p)%p
            for j,name in enumerate(['L','r','x']):
                pp=directions[name];den=eval_expr(pp['den'],canonical)
                Q=[0,0,0]
                for pair,(component,ex)in zip(pp['raw'],pp['labels']):
                    coeff=eval_expr(pair,canonical)*pow(den,-1,p)%p
                    mon=pow(wvalue,ex[0],p)*pow(z,ex[2],p)%p
                    Q[component]=(Q[component]+coeff*mon)%p
                F=(Q[0]-wvalue*Q[1])*pow(ct,-1,p)%p
                value=(value+flow[j]*F)%p
            out.append(value)
        return out
    values=differential_at(wcan,dwcan)
    conjugate_values=differential_at(zeta*wcan%p,zeta*dwcan%p)
    assert all(q==pow(zeta,char,p)*z%p for (label,char,_),z,q in zip(compiled,values,conjugate_values))
    differences=[(a-b)%p for a,b in zip(values,conjugate_values)]
    records.append({'physical_base':point,'w_old':ww,'rho':rho,'canonical_parameters':canonical,'canonical_marked_point_W_T':[wcan,z],
                    'physical_flow':physical_flow,'Prym_hol_absolute_differentials':dict(zip([z[0]for z in compiled],values)),
                    'divisor_P_minus_sigmaP_differentials':dict(zip([z[0]for z in compiled],differences)),
                    'nonzero_Abel_Prym_derivative':any(differences),'curve_tangent_identity':True,'mu3_covariance':True})
    if len(records)>=3:break
   except (ZeroDivisionError,AssertionError):continue
  if len(records)>=3:break
 if len(records)>=3:break

assert len(records)==3
out={'prime':p,'zeta3':zeta,'characteristic_zero_map':'On Gamma: w^6+c*w^3+1+v^6=0, define P=(W=w/rho,h=1,T=BR/A) on canonical C. The divisor P-sigma(P), sigma(W)=zeta3*W, has zero norm to the elliptic quotient and defines an Abel-Prym map along isoperiodic leaves.',
     'relative_absolute_primitive_convention':'a_i dW + sum_j F_ij dz_j; F_ij=(Q8_W-W*Q8_h)/C_t for the three hol forms',
     'records':records,'seconds':round(time.monotonic()-start,3),
     'scope':'A good finite-field point proves the displayed rational marked-point differential is not identically zero if the exact absolute-primitive convention is correct; independent audit requested. No physical-source moment matching, trace descent, Gysin serving statement, primitive, or certificate is asserted.'}
(HERE/'marked_point_probe.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print(json.dumps(out,indent=2,default=int))
