#!/usr/bin/env python3
"""Independent heat-adjoint and actual finite-field implementation audit.

Formal adjoints are derived as polynomial differential operators. For the
implementation comparison, invert the Jacobian of normalized moduli directly
using Fraction Taylor jets, derive H from its source-density transformation,
and only then reduce to F_1009. The tested search module is imported solely
to obtain implementation values; its geometric derivation is not imported.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product,permutations
from math import comb
import hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring
import verify_actual_lifts_fraction as jt
jt.ORDER=3
Jet=jt.Jet


def formal_checks():
    r=Ring(['u','d','e']);p=r.poly;z=(0,0,0);checks=[]
    def clean(a):return {k:v for k,v in a.items() if v}
    def plus(*args):
        out={}
        for a in args:
            for k,v in a.items():out[k]=r.add(out.get(k,{}),v)
        return clean(out)
    def scale(a,c):return clean({k:r.scale(v,c) for k,v in a.items()})
    def M(poly):return {z:poly} if poly else {}
    def D(i):
        k=[0,0,0];k[i]=1;return {tuple(k):r.const(1)}
    def deriv(poly,g):
        for i,n in enumerate(g):
            for _ in range(n):poly=r.diff(poly,r.names[i])
        return poly
    def compose(a,b):
        out={}
        for al,ca in a.items():
            for be,cb in b.items():
                for ga in product(*(range(n+1) for n in al)):
                    coeff=1
                    for n,m in zip(al,ga):coeff*=comb(n,m)
                    cp=r.scale(r.mul(ca,deriv(cb,ga)),coeff)
                    ex=tuple(x-y+w for x,y,w in zip(al,ga,be))
                    out[ex]=r.add(out.get(ex,{}),cp)
        return clean(out)
    def adjoint(a):
        out={}
        for al,ca in a.items():
            op={al:r.const((-1)**sum(al))}
            out=plus(out,compose(op,M(ca)))
        return out
    def check(name,a,b):
        assert not plus(a,scale(b,-1)),name
        checks.append(name)
    du,dd,de=[D(i) for i in range(3)]
    ddold=plus(dd,compose(M(p('-d/2')),du))
    cold=p('u+d**2/4')
    A0=plus(compose(M(r.scale(cold,Q(-1,3))),du),compose(M(p('-2*d/3')),ddold),compose(M(p('-e/6')),de))
    T0=plus(compose(M(r.scale(cold,Q(-1,3))),du),compose(M(p('-d/6')),ddold),compose(M(p('-2*e/3')),de))
    Tnew=plus(compose(M(p('-u/3')),du),compose(M(p('-d/6')),dd),compose(M(p('-2*e/3')),de))
    check('translation Euler field after triangular coordinate change',T0,Tnew)
    P1=plus(compose(de,de),scale(compose(plus(T0,M(p('1/6'))),du),-1))
    P2=plus(compose(ddold,ddold),scale(compose(plus(A0,M(p('-1/3'))),du),-1))
    expect1=plus(compose(de,de),scale(compose(du,plus(Tnew,M(p('-4/3')))),-1))
    expect2=plus(compose(dd,dd),compose(M(p('u/3')),compose(du,du)),
        compose(M(p('-d/3')),compose(dd,du)),compose(M(p('e/6')),compose(de,du)),compose(M(p('2/3')),du))
    check('P1 adjoint exact polynomial operator',adjoint(P1),expect1)
    check('P2 adjoint exact polynomial operator',adjoint(P2),expect2)
    check('P1 double adjoint',adjoint(adjoint(P1)),P1)
    check('P2 double adjoint',adjoint(adjoint(P2)),P2)
    return checks


def power_unit(x,a):
    assert x.value==1
    n=x-1;out=Jet(1);term=Jet(1);c=Q(1)
    for j in range(1,jt.ORDER+1):
        term=term*n;c*=Q(a-j+1,j);out=out+c*term
    return out


def determinant(a):
    out=Jet()
    for pm in permutations(range(3)):
        sign=(-1)**sum(pm[i]>pm[j] for i in range(3) for j in range(i+1,3))
        out=out+sign*a[0][pm[0]]*a[1][pm[1]]*a[2][pm[2]]
    return out


def geometry(r0,k0,z0):
    R0=Q(r0)**2;S0=Q(k0)**6/R0
    R,S,z=[jt.variable(v,i) for i,v in enumerate([R0,S0,Q(z0)])]
    k=k0*power_unit(R/R0,Q(1,6))*power_unit(S/S0,Q(1,6))
    A=1+R;B=1+S;T=1+z**6;C=k/3;D=z*k/2;E=z/2
    au,bu,tu=A/A.value,B/B.value,T/T.value
    ku=k/k0;zu=z/Q(z0)
    c=ku*power_unit(tu,Q(-1,3))*power_unit(au,Q(-1,3))*power_unit(bu,Q(-1,3))
    d=zu*ku*power_unit(tu,Q(-1,6))*power_unit(au,Q(-2,3))*power_unit(bu,Q(-1,6))
    e=zu*power_unit(tu,Q(-2,3))*power_unit(au,Q(-1,6))*power_unit(bu,Q(-1,6))
    coords=[c,d,e];jac=[[f.partial(i) for i in range(3)] for f in coords]
    fields=[]
    for j in range(3):
        fields.append(jt.solve(jac,[Jet(int(i==j)) for i in range(3)])[0])
    UC,UD,UE=fields
    def action(V,F):return sum((V[i]*F.partial(i) for i in range(3)),Jet())
    VA=[-c*UC[i]/3-2*d*UD[i]/3-e*UE[i]/6 for i in range(3)]
    VB=[-c*UC[i]/3-d*UD[i]/6-e*UE[i]/6 for i in range(3)]
    VT=[-c*UC[i]/3-d*UD[i]/6-2*e*UE[i]/3 for i in range(3)]
    logjac=[
        [1/(6*R)-1/(3*A),1/(6*S)-1/(3*B),-2*z**5/T],
        [1/(6*R)-2/(3*A),1/(6*S)-1/(6*B),1/z-z**5/T],
        [-1/(6*A),-1/(6*B),1/z-4*z**5/T]]
    jlog=determinant(logjac)
    Delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
    assert not (jlog-Delta/(36*R*S*z*A*B*T)).c
    # Source density: H=L*epsilon*mu/(c*d*e*J_log). Normalize at
    # the point; no closed H exponent formula is used here.
    L=power_unit(tu,Q(-1,6))*power_unit(au,Q(-1,6))*power_unit(bu,Q(-2,3))
    eps=power_unit(tu,Q(-2,3))*power_unit(au,Q(-1,6))*power_unit(bu,Q(-1,6))
    H=L*eps*(ku**-5)/(c*d*e)*(jlog.value/jlog)
    alpha=power_unit(tu,Q(-1,3))*power_unit(au,Q(-1,3))*power_unit(bu,Q(-1,3))
    def op1(F):
        return (action(UE,action(UE,F))/E.value**2
                -action(UC,action(VT,F)-Q(4,3)*F)/(C.value*T.value)).value
    def op2(F):
        return (A.value*action(UD,action(UD,F))/(T.value*D.value**2)
                -action(UC,action(VA,F)-Q(5,6)*F)/(C.value*T.value)).value
    def op3(F):
        G=F/alpha
        right=action(VT,G)-Q(5,3)*G
        right=action(VB,right)-Q(1,6)*right
        right=action(VA,right)-Q(7,6)*right
        return (A.value*B.value*action(UC,action(UC,action(UC,G)))/C.value**3-right/T.value).value
    rhs=(action(UE,action(UE,H))/E.value**2).value
    env=dict(R=R,S=S,z=z,k=k,A=A,B=B,T=T,Delta=Delta)
    return env,H,[op1,op2,op3],rhs,alpha


def main():
    checks=formal_checks();details=[]
    primary=HERE.parents[1]/'coupled-fresh/ruling-source/search_heat_multiplier.py'
    sha=hashlib.sha256(primary.read_bytes()).hexdigest()
    spec=importlib.util.spec_from_file_location('tested_heat_implementation',primary)
    impl=importlib.util.module_from_spec(spec);spec.loader.exec_module(impl)
    assert impl.P==1009 and impl.ORDER==3
    def mod(v):return v.numerator*pow(v.denominator,-1,impl.P)%impl.P
    def check(name,cond):
        assert cond,name
        checks.append(name)
    # Compatible rational points; denominators are checked again mod p.
    tests=[(1,1,Q(1)),(8,2,Q(2)),(1,2,Q(1,2)),(8,6,Q(-1)),(27,12,Q(3,2))]
    basis=['1','R','S','k','z','R*S+z*k','1/A','1/B','1/T','1/Delta','z**2/Delta']
    for i,pt in enumerate(tests):
        env,H,ops,rhs,alpha=geometry(*pt)
        mp=tuple(mod(Q(v)) for v in pt)
        penv,pH,pop,prhs,pop2,pop3=impl.prepare(*mp)
        comparejets={e:mod(v) for e,v in H.c.items() if mod(v)}
        check(f'{i}: H source-density third jet',comparejets==pH.c)
        check(f'{i}: forcing source value',mod(rhs)==prhs)
        for name in basis:
            F=H*jt.evaluate(name,env)
            pF=pH*impl.evaluate(name,penv)
            for j,(op,poperator) in enumerate(zip(ops,[pop,pop2,pop3])):
                check(f'{i}: P{j+1} implementation on H*({name})',mod(op(F))==poperator(pF))
        check(f'{i}: P3 alpha calibration',mod(ops[2](alpha))==mod(Q(35,108)/env['T'].value))
        details.append({'r':str(pt[0]),'k':str(pt[1]),'z':str(pt[2]),
            'rhs_exact':str(rhs),'rhs_mod_p':prhs,'P3_alpha_exact':str(ops[2](alpha))})
    # Any mutation during this audit invalidates its source binding.
    assert hashlib.sha256(primary.read_bytes()).hexdigest()==sha
    out={'status':'passed','count':len(checks),'checks':checks,'points':details,
        'implementation_sha256':sha,'prime':impl.P,'implementation_order':impl.ORDER,
        'method':'Formal sparse polynomial operator adjunction; independent exact Fraction third jets, normalized-moduli Jacobian inversion, density-derived H; implementation sampled only after independent computation',
        'P1_star':'partial_e²-partial_u(T0-4/3)',
        'P2_star':'partial_d²+(u/3)partial_u²-(d/3)partial_d partial_u+(e/6)partial_e partial_u+(2/3)partial_u',
        'P3_scaling':'epsilon² P3*(alpha_c^-1 F), alpha_c=(TAB)^-1/3, gives the implementation AB left product and1/T right product',
        'source_sign':'Search uses +H_ee; literal Green reconstruction for source -H chi_ee uses -H_ee. Negate a positive-RHS candidate when using that reconstruction convention.',
        'scope':'Local implementation checks and exact formal operator identities. No search was run, no candidate was accepted, and no bounded failure or global existence claim follows.'}
    (HERE/'heat-implementation-fraction-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))


if __name__=='__main__':main()
