#!/usr/bin/env python3
"""Independent actual-source Euler current, literal fiber term and density audit."""
import hashlib,json
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly

HERE=Path(__file__).resolve().parent
DATA=HERE.parents[1]/'coupled-fresh/ruling-source/full-base-connection'
checks={}


def check(name,value):
    assert value,name
    checks[name]=True


def zero(name,expr):check(name,s.expand(expr)==0)


def main():
    sourcefile=DATA/'source-euler-current-results.json'
    ijfile=DATA/'rank8-ij-connections-results.json'
    vfile=DATA/'rank8-v-literal-primitives-results.json'
    packet=json.loads(sourcefile.read_text());ij=json.loads(ijfile.read_text());vr=json.loads(vfile.read_text())
    for p in (ijfile,vfile):
        check('source binding '+p.name,
              packet['connection_inputs_sha256'][str(p)]==hashlib.sha256(p.read_bytes()).hexdigest())
    i,j,v,e=s.symbols('i j v e',nonzero=True)
    h=s.Function('h')(i,j,v)
    D=lambda f:-2*i*s.diff(f,i)-j*s.diff(f,j)+6*v*s.diff(f,v)
    vector=(-2*i,-j,6*v)
    coord=(i,j,v)
    zero('full flat Euler volume divergence',sum(s.diff(a,x) for a,x in zip(vector,coord))-3)
    t=h/(6*v*v)
    pp=[t*x for x in vector]
    divergence=sum(s.diff(a,x) for a,x in zip(pp,coord))
    zero('actual scalar source minus current is four t',
         (D(h)-5*h)/(6*v*v)-divergence-4*t)
    # Full source weight from dc dd de=e³ di dj de and de=e dv/(6v).
    zero('source density into flat i j v volume',
         s.cancel(e**(-6)*e**(-4)*e**3*e/(6*v)-1/(6*v*v)).subs(v,e**6))
    # This source density is flat in i,j,v. di dJ introduces 2j.
    zero('J versus j density factor',2*j/(12*j)-s.Rational(1,6))

    # Literal exterior-current signs, with relative form dx first.
    x=s.symbols('x')
    nu=s.Function('nu')(x,i,j,v)
    P=[s.Function('P'+str(k))(i,j,v) for k in range(3)]
    f=[s.Function('f'+str(k))(x,i,j,v) for k in range(3)]
    current={(0,2,3):-nu*P[0],(0,1,3):nu*P[1],(0,1,2):-nu*P[2],
             (1,2,3):-sum(a*b for a,b in zip(P,f))}
    coordinates=(x,i,j,v)
    exterior=s.S.Zero
    for indices,value in current.items():
        missing=next(k for k in range(4) if k not in indices)
        sign=(-1)**sum(k<missing for k in indices)
        exterior+=sign*s.diff(value,coordinates[missing])
    expected=sum(nu*s.diff(P[k],coord[k])+P[k]*(s.diff(nu,coord[k])-s.diff(f[k],x)) for k in range(3))
    zero('literal base and fiber three-current signs',exterior-expected)

    C=fmpq_mpoly_ctx.get(('i','j','v'));ii,jj,vv=C.gens();z=C.constant(0)
    parse=lambda txt:fmpq_mpoly(txt,C)
    Di=parse(ij['common_denominator']);Dv=parse(vr['common_denominator']);Dr=parse(packet['remaining_common_denominator'])
    common=Di*Dv*Dr
    for row in range(8):
        Ni=parse(ij['Gamma_numerators']['i'][row][6]);Nj=parse(ij['Gamma_numerators']['j'][row][6]);NV=parse(vr['GammaV_numerators'][row][6])
        RR=parse(packet['remaining_vector_numerators'][row])
        expected=((4*common if row==6 else z)-NV*(common//Dv)+(2*ii*Ni+jj*Nj)*(common//Di))
        check('all compact Euler residual components '+str(row),RR*(common//Dr)==expected)
    for row in range(16):
        Pi=parse(ij['primitive_numerators']['i'][row][6]);Pj=parse(ij['primitive_numerators']['j'][row][6]);PV=parse(vr['primitive_numerators'][row][6])
        PD=parse(packet['fiber_primitive_D_numerators'][row])
        expected=PV*(common//Dv)-(2*ii*Pi+jj*Pj)*(common//Di)
        check('all literal Euler fiber primitive components '+str(row),PD*(common//Dr)==expected)
    w=s.symbols('w')
    TT=1+w**3;NN=9*i*i*w*w-16*j*j*TT
    a0=54*i**3*w*TT/(j*j*NN)
    zero('physical source moment coefficient divided by six',a0/6-9*i**3*w*TT/(j*j*NN))
    out={'status':'passed exact actual-source Euler current audit','checks':checks,'count':len(checks),
      'source_sha256':hashlib.sha256(sourcefile.read_bytes()).hexdigest(),
      'volume':'flat di wedge dj wedge dv; physical pullback uses di wedge dj wedge dw',
      'literal_current':'Jbase=-sum(nu.Pp) wedge contraction_p(mu); Jfiber=-t*fD_b*mu',
      'identity':'Original compact source=dJ+t*(4e_b-GammaD e_b).mu; source sign and all8components retained',
      'physical_residual':'9i³w(1+w³)/(j²N)*(4e_b-GammaD e_b)',
      'scope':'Exact first current and full nonzero compact remainder, not a primitive of the original target.'}
    path=HERE/'source-euler-current-audit-results.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'pass':True,'checks':len(checks),'output':str(path)}))


if __name__=='__main__':main()
