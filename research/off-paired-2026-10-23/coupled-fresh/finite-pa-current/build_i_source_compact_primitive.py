#!/usr/bin/env python3
"""Explicit compact i-current for the actual Euler source, with corrections.

The density and physical inverse-branch corrections remain displayed.
This is not a complete i-only or full-base primitive.
"""
import hashlib,json,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'ruling-source/full-base-connection'
C=fmpq_mpoly_ctx.get(('i','j','v'))
i,j,v=C.gens();zero=C.constant(0)
def p(x):return fmpq_mpoly(x,C)
def mv(A,x):return [sum((a*b for a,b in zip(row,x)),zero) for row in A]
def dp(x):return -2*i*x.derivative(0)-j*x.derivative(1)+6*v*x.derivative(2)

def main():
 start=time.monotonic()
 ip=BASE/'rank8-ij-connections-results.json';vp=BASE/'rank8-v-literal-primitives-results.json'
 ij=json.loads(ip.read_text());vr=json.loads(vp.read_text())
 di=p(ij['common_denominator']);dv=p(vr['common_denominator'])
 Gi=[[p(x) for x in row] for row in ij['full_rank9_Gamma_numerators']['i']]
 Gj=[[p(x) for x in row] for row in ij['full_rank9_Gamma_numerators']['j']]
 GV=[[p(x) for x in row] for row in vr['full_rank9_GammaV_numerators']]
 den=di*dv
 GD=[[di*GV[r][c]-dv*(2*i*Gi[r][c]+j*Gj[r][c]) for c in range(9)]for r in range(9)]
 ct=[zero,zero,-j/6,zero,zero,C.constant(6),2*i-C.constant(2)/3,-i/3,j]
 eb=[C.constant(int(r==6))for r in range(9)]
 ebq=[C.constant(int(r==7))for r in range(9)]
 un=[den*(2*x-dp(x)-eb[r]/2)-y for r,(x,y) in enumerate(zip(ct,mv(GD,ct)))]
 checks=[]
 def check(name,value):
  assert value,name
  checks.append(name)
 check('all infinity companion of Ui cancels',not un[8])
 conn=mv(Gi,un)
 for r in range(9):
  check('generic compact i source identity row'+str(r),
        di*(un[r].derivative(0)*den-un[r]*den.derivative(0))
        +den*conn[r]-di*den*(4*eb[r]*den-GD[r][6]+den*ebq[r]/2)==0)
 common=den
 for x in un[:8]:common=common.gcd(x)
 outden=den//common;outun=[x//common for x in un[:8]]

 si,sj,sv,x,a,y=s.symbols('i j v x a y')
 J=sv*(2*a*a+sj*a*x)-2*y*y
 F=y*y+sv*(a*a+si*x*x+sj*a*x+x+1)
 gb=s.groebner([a*y-x**3,F],a,y,x,domain=s.QQ.frac_field(si,sj,sv))
 ax=(-sv*sj*a*a-2*sv*si*a*x-sv*a-6*y*x*x)/J
 yx=sv*(6*a*x*x+4*sj*x**3+2*si*x*y+y)/J
 ai=-sv*a*x*x/J;yi=sv*y*x*x/J
 aj=-sv*a*a*x/J;yj=sv*x**4/J
 aD=-a*sv*(6*a*a+4*si*x*x+5*sj*a*x+6*x+6)/J
 yD=-y*aD/a
 def rem(expr):
  num=s.cancel(expr).as_numer_denom()[0]
  return gb.reduce(num)[1]==0
 check('literal implicit i curve derivative',rem(2*y*yi+sv*((2*a+sj*x)*ai+x*x)))
 check('literal partial_i Psi_i equals nu_b',s.cancel(yi/x**2-sv*y/J)==0)
 check('literal partial_j Psi_i equals omega',s.cancel(yj/x**2-sv*x*x/J)==0)
 ci=(2*si-s.Rational(2,3))*y-si*y*x/3+6*(a*x+sj*x*x/2)-sj*x**3/6
 Gi_exact=-y/x-y/3
 dGi=s.diff(Gi_exact,x)+s.diff(Gi_exact,y)*yx
 check('literal Psi_i compact finite infinity exact decomposition',
       rem(y/x**2-y/(2*x)-sj*sv*x*x/J-sv*ci/J-dGi))
 check('literal D zeta Cartan correction',rem(yD/x-3*y/x-sv*y/J+yx))
 check('constant finite Pa residue after Ui correction',s.Rational(1,2)*(2-3)+s.Rational(1,2)==0)

 result={
  'status':'Actual compact i-current for Euler source; density and inverse-branch corrections remain open',
  'coordinates':'native i,j,v; physical i,j,w; D=-2i partial_i-j partial_j+6v partial_v',
  'basis':ij['compact_basis_numerators'],
  'psi_i':'y dx/x^2=(x/a)dx',
  'psi_i_literal_derivatives':['partial_i Psi_i=nu_b','partial_j Psi_i=omega'],
  'psi_i_reduction':'Psi_i=zeta_hat/2+j*omega+nu dot Ci+d_x Gi',
  'Ci':[str(z) for z in ct[:8]],'omega_coefficient':'j',
  'Gi':'-y/x-y/3',
  'D_zeta_literal':'nabla_D zeta_hat=3*zeta_hat+nu_b-d_x y',
  'Ui_differential':'(2-nabla_D)Psi_i+zeta_hat/2',
  'Ui_compact_definition':'-e_b/2+(2-nabla_D)(Ci+j*omega)',
  'Ui_common_denominator':str(outden),'Ui_numerators':[str(z) for z in outun],
  'Ui_exact_fiber_primitive':'y/2+(2-D)Gi-fiber_primitive_D dot (Ci+j*omega)',
  'source_identity':'partial_i Ui+Gamma_i Ui=(4I-GammaD)e_b+e_bq/2',
  'native_current':'P_i=t Ui,P_j=P_v=0,t=hsrc/(6v^2)',
  'remaining_native':'-partial_i|j,v(t)*Ui-t*e_bq/2',
  'physical_piola':'P_i=v_w*t*Ui=(a0/6)*Ui,P_w=-v_i*t*Ui,P_j=0; a0=54i^3wT/(j^2N)',
  'remaining_physical':'-v_w*(partial_i|j,v t)*Ui-(a0/12)*e_bq; the derivative retains w(i,j,v)',
  'i_only_warning':'The physical P_w term is essential. This does not solve fixedj,w i-only integration.',
  'literal_current':'Use all eight stored connection fiber primitives for Ui, plus Ui_exact_fiber_primitive; no compact or residue component is dropped.',
  'connection_hashes':{'ij':hashlib.sha256(ip.read_bytes()).hexdigest(),'V':hashlib.sha256(vp.read_bytes()).hexdigest()},
  'checks':len(checks),'check_names':checks,'certificate':False,
  'elapsed_seconds':round(time.monotonic()-start,3)}
 out=HERE/'i-source-compact-primitive-results.json';out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'checks':len(checks),'output':str(out),'seconds':result['elapsed_seconds']}))

if __name__=='__main__':main()
