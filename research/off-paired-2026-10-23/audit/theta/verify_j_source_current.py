#!/usr/bin/env python3
"""Independent source-serving j primitive, literal reduction and Piola audit."""
import hashlib,json
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly

HERE=Path(__file__).resolve().parent
DATA=HERE.parents[1]/'coupled-fresh/ruling-source/full-base-connection'
C=fmpq_mpoly_ctx.get(('i','j','v'));ii,jj,vv=C.gens();zero=C.constant(0)
checks={}


def check(name,x):
    assert x,name
    checks[name]=True


def clearcheck(name,x):check(name,s.cancel(x)==0)


def main():
    path=DATA/'j-source-primitive-results.json';raw=json.loads(path.read_text())
    ipath=DATA/'rank8-ij-connections-results.json';vpath=DATA/'rank8-v-literal-primitives-results.json'
    ij=json.loads(ipath.read_text());vp=json.loads(vpath.read_text())
    parse=lambda x:fmpq_mpoly(x,C)
    for label,p in [('ij',ipath),('V',vpath)]:
        check('audited connection hash '+label,raw['connection_hashes'][label]==hashlib.sha256(p.read_bytes()).hexdigest())
    Di=parse(ij['common_denominator']);Dv=parse(vp['common_denominator']);DU=parse(raw['U_common_denominator'])
    Gi=[[parse(x) for x in row] for row in ij['full_rank9_Gamma_numerators']['i']]
    Gj=[[parse(x) for x in row] for row in ij['full_rank9_Gamma_numerators']['j']]
    GV=[[parse(x) for x in row] for row in vp['full_rank9_GammaV_numerators']]
    ct=[parse(x) for x in raw['ctheta']]
    U=[parse(x) for x in raw['U_numerators']]+[zero]
    simple=[vv*(5*jj*jj-12*ii)/48,vv*(5*jj*jj-12*ii)/48,C.constant(-1),C.constant(2),
            -5*jj*vv/24,jj*vv*(15*jj*jj-52*ii)/96,zero,-jj/2,zero]
    D=lambda x:-2*ii*x.derivative(0)-jj*x.derivative(1)+6*vv*x.derivative(2)
    GD=[[Di*GV[r][col]-Dv*(2*ii*Gi[r][col]+jj*Gj[r][col]) for col in range(9)] for r in range(9)]
    den=Di*Dv
    for r in range(9):
        check('all nine Psi_j parameter derivative entries '+str(r),
              Di*(ct[r].derivative(1)-(1 if r==6 else 0))+sum((Gj[r][k]*ct[k] for k in range(9)),zero)==0)
        actual=den*(3*ct[r]-D(ct[r]))-sum((GD[r][k]*ct[k] for k in range(9)),zero)
        check('full Euler shifted U definition '+str(r),actual*DU==U[r]*den)
        check('simple polynomial U coefficient '+str(r),U[r]==DU*simple[r])
        lhs=Di*den*U[r].derivative(1)+den*sum((Gj[r][k]*U[k] for k in range(9)),zero)
        rhs=DU*Di*((4*den if r==6 else zero)-GD[r][6])
        check('actual Euler source served by nabla_j U '+str(r),lhs==rhs)
    check('all infinity residue entries cancel',not U[8])

    # Independent literal fiber reduction through the single quartic root.
    i,j,v,x,y=s.symbols('i j v x y',nonzero=True)
    a=x**3/y;V=i*x*x+x+1
    P=y**4+v*V*y*y+j*v*x**4*y+v*x**6
    Jbar=2*v*x**6/y**2+j*v*x**4/y-2*y*y
    yj=v*x**4/Jbar
    yx=-s.diff(P,x)/s.diff(P,y)
    def modzero(name,f):
        numerator=s.cancel(f).as_numer_denom()[0]
        check(name,s.rem(numerator,P,y)==0)
    # Restore the serialized source primitive; no primary reduction is imported.
    A=s.symbols('a')
    G=s.sympify(raw['fiber_primitive'],locals={'i':i,'j':j,'v':v,'x':x,'y':y,'a':A}).subs(A,a)
    basis=[1,x,x**3,x**4-v*(i-j*j/4)*(i-5*j*j/4)*x*x/8,a,a*x+j*x*x/2,y,y*x,x*x]
    cs=[s.sympify(str(z).replace('^','**'),locals={'i':i,'j':j,'v':v}) for z in ct]
    modzero('literal Psi_j nine-class and fiber reduction',
            y*y/(2*x**4)-v*sum(z*b for z,b in zip(cs,basis))/Jbar-s.diff(G,x)-s.diff(G,y)*yx)
    clearcheck('literal Psi_j derivative is nu_b',y*yj/x**4-v*y/Jbar)

    # Full source density is not j-constant. The retained residual is mandatory.
    w=s.symbols('w');t=s.Function('t')(i,j,w);vj=s.Function('vj')(i,j,w);vw=s.Function('vw')(i,j,w)
    Ufun=s.Function('U')(i,j,w)
    native_j=lambda f:s.diff(f,j)-vj*s.diff(f,w)/vw
    clearcheck('density product derivative retains correction',
               native_j(t*Ufun)-t*native_j(Ufun)-native_j(t)*Ufun)
    clearcheck('physical remainder keeps root derivative',
               -vw*native_j(t)*Ufun-(vj*s.diff(t,w)-vw*s.diff(t,j))*Ufun)
    # Piola current: Pj_phys=vw*tU, Pw_phys=-vj*tU. Mixed v derivatives agree.
    piola_div=s.diff(vw*t*Ufun,j)-s.diff(vj*t*Ufun,w)
    clearcheck('full physical Piola divergence including Jacobian',
               piola_div-vw*native_j(t*Ufun)-(s.diff(vw,j)-s.diff(vj,w))*t*Ufun)
    fj,fV=s.symbols('f_j f_V')
    clearcheck('all physical fiber Cartan terms retained and cancel correctly',
               vw*t*(fj+vj*fV/(6*v))-vj*t*(vw*fV/(6*v))-vw*t*fj)
    out={'status':'passed exact source-serving j primitive audit','checks':checks,'count':len(checks),
      'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
      'U_simple':[str(x) for x in simple[:8]],
      'actual_current':'Pj=tU, t=hsrc/(6v²), flat i,j,v volume',
      'retained_source':'-partial_j(t)|i,v * U; physical density is -v_w*partial_j(t)|i,v*U',
      'scope':'All compact and infinity entries, Euler shifts, literal Psi_j primitive, covariant source equation, density correction and physical Piola/fiber terms. Density residual remains unserved; no certificate.'}
    p=HERE/'j-source-current-audit-results.json';p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'pass':True,'checks':len(checks),'output':str(p)}))


if __name__=='__main__':main()
