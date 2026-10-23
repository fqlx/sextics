#!/usr/bin/env python3
"""An explicit all-eight-component horizontal primitive for the Euler source.

Psi_j=y^2 dx/(2x^4), partial_j Psi_j=nu_y literally. Its compact+omega
reduction gives a rational pure-compact U with nabla_j U=(4-nabla_D)nu_y.
The density correction -t_j U is retained, not declared integrated.
"""
from pathlib import Path
import hashlib,json,time
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly

HERE=Path(__file__).resolve().parent
CTX=fmpq_mpoly_ctx.get(('i','j','v'))
i,j,v=CTX.gens();zero=CTX.constant(0)

def P(x):return fmpq_mpoly(x,CTX)
def mv(A,x):return [sum((a*b for a,b in zip(row,x)),zero)for row in A]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),zero)
def Dp(x):return -2*i*x.derivative(0)-j*x.derivative(1)+6*v*x.derivative(2)

def main():
    start=time.monotonic()
    ijpath=HERE/'rank8-ij-connections-results.json'
    vpath=HERE/'rank8-v-literal-primitives-results.json'
    ij=json.loads(ijpath.read_text());vr=json.loads(vpath.read_text())
    dij=P(ij['common_denominator']);dv=P(vr['common_denominator'])
    Gi=[[P(x)for x in row]for row in ij['full_rank9_Gamma_numerators']['i']]
    Gj=[[P(x)for x in row]for row in ij['full_rank9_Gamma_numerators']['j']]
    GV=[[P(x)for x in row]for row in vr['full_rank9_GammaV_numerators']]
    den=dij*dv
    GD=[[dij*GV[r][c]-dv*(2*i*Gi[r][c]+j*Gj[r][c])for c in range(9)]for r in range(9)]
    ct=[-v*(4*i-1)*(12*i-5*j*j)/144,
        -v*(4*i-1)*(12*i-5*j*j)/144,
        CTX.constant(1)/3,2*(4*i-1)/3,
        -5*j*v*(4*i-1)/72,
        -j*v*(4*i-1)*(52*i-15*j*j)/288,
        4*j/3,j/6,CTX.constant(2)]
    eb=[CTX.constant(int(r==6))for r in range(9)]
    checks=[]
    def check(name,value):
        assert value,name
        checks.append(name)
    connection=mv(Gj,ct)
    for r in range(9):
        check(f'generic nabla_j ctheta equals eb row{r}',
              dij*(ct[r].derivative(1)-eb[r])+connection[r]==0)
    un=[den*(3*x-Dp(x))-y for x,y in zip(ct,mv(GD,ct))]
    check('U infinity companion cancels identically',un[8]==0)
    # Check the full generic source identity, without assuming flatness.
    gjun=mv(Gj,un)
    for r in range(9):
        check(f'generic nabla_j U actual Euler source row{r}',
              dij*(un[r].derivative(1)*den-un[r]*den.derivative(1))
              +den*gjun[r]
              -dij*den*(4*eb[r]*den-GD[r][6])==0)
    common=den
    for x in un[:8]:common=common.gcd(x)
    den=den//common;un=[x//common for x in un[:8]]
    check('U denominator is a coefficient-field constant',den.degrees()==(0,0,0))
    denvalue=den.to_dict()[(0,0,0)]
    un=[z/denvalue for z in un]
    den=CTX.constant(1)
    # Keep the exact fiber correction of the new j current itself.
    fj=[[P(x)for x in row]for row in ij['primitive_numerators']['j']]
    fjun=[dot(row,un)for row in fj]
    fiberden=dij
    for z in fjun:fiberden=fiberden.gcd(z)
    fibercommon=dij//fiberden
    fjun=[z//fiberden for z in fjun]
    if fibercommon.degrees()==(0,0,0):
        z=fibercommon.to_dict()[(0,0,0)]
        fjun=[p/z for p in fjun];fibercommon=CTX.constant(1)
    # Literal fiber reduction of Psi_j; this check uses no connection data.
    si,sj,sv,x,a,y=s.symbols('i j v x a y')
    c=(1-4*si)/12
    cx=-sv*(4*si-1)*(12*si+5*sj**2)/288
    ca=-5*sj*sv*(4*si-1)/72
    F=y**2*(-1/(6*x**3)-1/(12*x**2)+c/x)
    G=F+cx*x+ca*a
    Jbar=sv*(2*a*a+sj*a*x)-2*y*y
    yx=sv*(6*a*x*x+4*sj*x**3+2*si*x*y+y)/Jbar
    ax=(-sv*sj*a*a-2*sv*si*a*x-sv*a-6*y*x*x)/Jbar
    basis=[1,x,x**3,x**4-sv*(si-sj**2/4)*(si-5*sj**2/4)*x*x/8,
           a,a*x+sj*x*x/2,y,y*x,x*x]
    symct=[s.sympify(str(z).replace('^','**'),locals={'i':si,'j':sj,'v':sv})for z in ct]
    numerator=s.cancel((y*y/(2*x**4)-sv*sum(z*b for z,b in zip(symct,basis))/Jbar
                        -s.diff(G,x)-s.diff(G,a)*ax-s.diff(G,y)*yx)*2*x**4*Jbar)
    num,dd=s.fraction(numerator)
    gb=s.groebner([a*y-x**3,y*y+sv*(a*a+si*x*x+sj*a*x+x+1)],a,y,x,
                  domain=s.QQ.frac_field(si,sj,sv))
    check('literal rational Psi_j compact+omega+fiber reduction',gb.reduce(num)[1]==0)
    yj=sv*x**4/Jbar
    aj=-a*yj/y
    implicit=s.cancel((2*y*yj+sv*((2*a+sj*x)*aj+a*x))*Jbar*y)
    check('literal implicit j derivative solves both curve equations',gb.reduce(s.fraction(implicit)[0])[1]==0)
    check('literal partial_j Psi_j equals nu_b',s.cancel(y*yj/x**4-sv*y/Jbar)==0)
    # A second pure-compact j primitive, for the bq row used in the
    # source-specific weighted N-pole current.
    w7=[-5*v*(4*i-j*j)/48,-v*(16*i*i+12*i-5*j*j)/48,
        CTX.constant(3),CTX.constant(2),-j*v*(4*i+5)/24,
        -j*v*(52*i-15*j*j)/96,zero,2*j,zero]
    jw7=mv(Gj,w7)
    for r in range(9):
        check(f'generic compact j primitive of ebq row{r}',
              dij*(w7[r].derivative(1)-CTX.constant(int(r==7)))+jw7[r]==0)
    F7=-y*y/(4*x*x)-y*y/(4*x)
    cx7=-sv*(12*si+5*sj*sj)/96
    ca7=-5*sj*sv/24
    G7=F7+cx7*x+ca7*a
    beta7=y*y/(2*x**3)+sv*si*(1/x-yx/(3*y))/2
    sw7=[s.sympify(str(z).replace('^','**'),locals={'i':si,'j':sj,'v':sv})for z in w7]
    expr7=s.cancel((beta7-sv*sum(z*b for z,b in zip(sw7,basis))/Jbar
                    -s.diff(G7,x)-s.diff(G7,a)*ax-s.diff(G7,y)*yx)*x**3*Jbar)
    check('literal compact beta7 fiber reduction',gb.reduce(s.fraction(expr7)[0])[1]==0)
    result={
      'status':'Actual full-base source primitive; density correction retained, no sextic certificate',
      'coordinates':'i,j,v; D=-2i partial_i-j partial_j+6v partial_v',
      'basis':ij['compact_basis_numerators']+['omega: x^2'],
      'psi_j':'y^2 dx/(2x^4)',
      'literal_relation':'partial_j Psi_j=nu_b',
      'ctheta':[str(z)for z in ct],
      'fiber_primitive':str(G),
      'reduction':'Psi_j=nu dot ctheta+d_x G; ninth coefficient is 2*omega',
      'U_definition':'U=(3I-GammaD)ctheta-D(ctheta); its ninth component is identically zero',
      'U_common_denominator':str(den),
      'U_numerators':[str(z)for z in un],
      'U_simplified_polynomial_vector':[str(z)for z in un],
      'Wbq_polynomial_vector':[str(z)for z in w7[:8]],
      'Wbq_source_identity':'partial_j Wbq+Gamma_j Wbq=e_bq (row7), no infinity or finite third-kind component',
      'Wbq_literal_form':'beta7=y^2 dx/(2x^3)+(v*i/2)*(dlog(x)-dlog(y)/3); beta7=nu dot Wbq+d_x G7',
      'Wbq_fiber_primitive':str(G7),
      'Wbq_j_fiber_identity':'partial_j beta7=nu_bq-d_x(v^2*i*a*x/(6*Jbar))',
      'source_identity':'partial_j U+Gamma_j U=(4I-GammaD)e_b',
      'native_current':'P_j=t U, P_i=P_v=0, t=hsrc/(6v^2)',
      'remaining_native':'-partial_j(t)|i,v * U, with all physical w(i,j,v) derivatives retained',
      'fiber_current':'-t*(fiber_primitive_j dot U)*di wedge dj wedge dv, using all eight stored literal j primitives',
      'fiber_primitive_jU_words':ij['primitive_words'],
      'fiber_primitive_jU_numerators':[str(z)for z in fjun],
      'fiber_primitive_jU_common_denominator':str(fibercommon),
      'fiber_primitive_jU_convention':'sum_word numerator[word]*word/(common_denominator*Jbar)',
      'physical_piola':'For volume di dj dw: P_j=v_w*t*U=(a0/6)*U, P_w=-v_j*t*U, P_i=0. Remaining density=-v_w*(partial_j|i,v t)*U.',
      'connection_hashes':{'ij':hashlib.sha256(ijpath.read_bytes()).hexdigest(),'V':hashlib.sha256(vpath.read_bytes()).hexdigest()},
      'checks':len(checks),'check_names':checks,'certificate':False,
      'elapsed_seconds':time.monotonic()-start,
    }
    (HERE/'j-source-primitive-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':len(checks),'status':result['status'],'seconds':result['elapsed_seconds']},indent=2))

if __name__=='__main__':main()
