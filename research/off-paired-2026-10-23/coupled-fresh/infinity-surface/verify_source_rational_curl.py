#!/usr/bin/env python3
"""Exact source surface and log-free rational partial infinity current.

Constructive identities only. No completed closed extension or certificate.
Python standard library; uses the independently written polynomial routines.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'audit'))
from verify_connection_fraction import Ring
sys.path.insert(0,str(ROOT/'audit/quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks=[]
    def check(name,r):
        assert not r,(name,r)
        checks.append(name)
    r=LaurentRing(['a','H','C','z']);p=r.laurent
    q=p('3*C-3*a*z/2')
    P=r.add(p('a**4+a**2*(z**6+1-H)'),r.power(q,6),r.mul(p('a**2*z/2'),q))
    Pa,PC,Pz=[r.diff(P,v) for v in ['a','C','z']]
    rho=r.mul(r.power(q,3),p('1/a**2'));kk=r.mul(r.power(q,2),p('9/(2*a**2)'))
    # eta=-rho/2*d(az), using full ordinary d(a,C,z).
    eta=[r.mul(rho,p('-z/2')),{},r.mul(rho,p('-a/2'))]
    for i,j,want,name in [(0,1,r.mul(kk,p('z')),'aC'),(0,2,rho,'az'),(1,2,r.mul(kk,p('-a')),'Cz')]:
        names=['a','C','z']
        got=r.add(r.diff(eta[j],names[i]),r.scale(r.diff(eta[i],names[j]),-1))
        check('actual_density_primitive_'+name,r.add(got,r.scale(want,-1)))
    # L=k Dz(az)-rho*a_C. Clear Pa; a_C=-PC/Pa, a_z=-Pz/Pa.
    Ln=r.add(r.mul(kk,r.add(r.mul(p('a'),Pa),r.scale(r.mul(p('z'),Pz),-1))),r.mul(rho,PC))
    Lsmall=r.mul(r.power(q,2),r.add(p('9*H-36*z**6-9'),r.mul(q,p('-21*z/4'))))
    check('simplified_actual_L_mod_P',r.add(Ln,r.scale(Lsmall,-1),r.scale(r.mul(r.mul(r.power(q,2),p('1/a**2')),P),-18)))
    eta_zn=r.mul(rho,r.scale(r.add(r.mul(p('a'),Pa),r.scale(r.mul(p('z'),Pz),-1)),Q(-1,2)))
    Jn=r.add(eta_zn,r.mul(p('2*C/3'),Ln))
    Jsmall=r.mul(r.mul(r.power(q,2),p('1/12')),r.add(
        r.mul(p('36*H'),r.add(r.mul(p('a*z'),r.const(1)),q)),
        r.mul(p('-24*a**2-21*a*z**2-72*z**6-36'),q),
        p('-144*a*z**7-36*a*z'),r.mul(p('-17*z'),r.power(q,2))))
    check('simplified_actual_J_mod_P',r.add(Jn,r.scale(Jsmall,-1),r.scale(r.mul(r.mul(p('C/a**2'),r.power(q,2)),P),-12)))
    # Verify the complete physical pullback of d eta to a normalized leaf.
    # Coefficients T(a)=(a²-alpha PC)/Pa, Dz(a)=-Pz/Pa.
    alpha=p('2*C/(3*H)')
    ta_n=r.add(p('a**2'),r.scale(r.mul(alpha,PC),-1))
    # In d eta =rho da^dz-k dC^d(az), substitute dC=alpha*dH.
    # rho*T(a)-alpha*k*Dz(az) = phi-alpha*L.
    leafn=r.add(r.mul(rho,ta_n),r.scale(r.mul(r.mul(alpha,kk),r.add(r.mul(p('a'),Pa),r.scale(r.mul(p('z'),Pz),-1))),-1))
    check('full_physical_leaf_density_identity',r.add(leafn,r.scale(r.power(q,3),-1),r.mul(alpha,Ln)))
    # Generic curl algebra. A=B theta commutes T,Dz and H, but not C.
    # Treat A(eta_H),A(eta_z),A(alpha L) and their T,Dz derivatives as
    # arbitrary jets. The relation A(phi)=T Aeta_z-Dz Aeta_H+A(alpha L)
    # is the differentiated exact leaf identity.
    g=LaurentRing(['H','Aphi','AeH_z','Aez_H','Aez','AalphaL']);gp=g.laurent
    target=gp('-Aphi/(9*H)')
    curl=gp('AeH_z/(9*H)-Aez_H/(9*H)+Aez/(9*H**2)')
    remainder=gp('-Aez/(9*H**2)-AalphaL/(9*H)')
    diff=g.add(target,g.scale(curl,-1),g.scale(remainder,-1))
    # Substitute Aphi=Aez_H-AeH_z+AalphaL, an exact linear identity.
    sub={v:gp(v) for v in g.names};sub['Aphi']=gp('Aez_H-AeH_z+AalphaL')
    # Only H has a negative exponent, and its substitution is itself.
    out={}
    for ex,co in diff.items():
        term=g.const(co)
        for name,k in zip(g.names,ex):
            if k<0:
                assert name=='H';term=g.mul(term,{tuple(k if v=='H' else 0 for v in g.names):Q(1)})
            else:term=g.mul(term,g.power(sub[name],k))
        out=g.add(out,term)
    check('complete_operator_partial_curl_sign',out)
    # Actual root-cover surface and source residue.
    s=Ring(['a','tau','b','z']);sp=s.poly
    qq=sp('3*b*tau**2-3*a*z/2');QQ=s.power(qq,3)
    PP=s.add(sp('a**4+a**2*(z**6+1-tau**3)'),s.power(qq,6),s.mul(sp('a**2*z/2'),qq))
    PA=s.diff(PP,'a');PAA=s.diff(PA,'a');PB=s.diff(PP,'b')
    # Parameter derivative at fixed tau,z, including a_b=-Pb/Pa.
    dphi=s.add(s.mul(s.add(s.mul(s.diff(QQ,'b'),PA),s.scale(s.mul(QQ,s.diff(PA,'b')),-1)),PA),
        s.scale(s.mul(PB,s.add(s.mul(s.diff(QQ,'a'),PA),s.scale(s.mul(QQ,PAA),-1))),-1))
    # Direct simple/double pole normal residue of partial_b(Q/P).
    res=s.add(s.mul(s.mul(s.diff(QQ,'b'),PA),PA),
        s.scale(s.mul(s.add(s.mul(s.diff(QQ,'a'),PB),s.mul(QQ,s.diff(PB,'a'))),PA),-1),s.mul(s.mul(QQ,PB),PAA))
    check('actual_parameter_residue_matches_all_a_b_jets',s.add(dphi,s.scale(res,-1)))
    check('theta_vs_tau_actual_P',s.add(s.mul(sp('b'),s.diff(PP,'b')),s.scale(s.mul(sp('tau'),s.diff(PP,'tau')),Q(-1,2)),sp('-3*a**2*tau**3/2')))
    # Clear P² in theta(Q/P)-(tau/2)partial_tau(Q/P)
    # +(3/2)a²tau³ Q/P²=0.
    jet=s.add(s.mul(sp('b'),s.add(s.mul(s.diff(QQ,'b'),PP),s.scale(s.mul(QQ,s.diff(PP,'b')),-1))),
        s.scale(s.mul(sp('tau'),s.add(s.mul(s.diff(QQ,'tau'),PP),s.scale(s.mul(QQ,s.diff(PP,'tau')),-1))),Q(-1,2)),
        s.mul(sp('3*a**2*tau**3/2'),QQ))
    check('exact_ambient_surface_partial_potential',jet)
    # Fixed(H,z) source curve: source-carrying elliptic decomposition.
    e=LaurentRing(['a','q','K','z']);ep=e.laurent
    EP=ep('a**4+a**2*(K+z*q/2)+q**6')
    ss=ep('a+q**3/a');dd=ep('a-q**3/a');LL=ep('K+z*q/2')
    check('actual_source_elliptic_plus',e.add(e.power(ss,2),ep('-2*q**3+z*q/2+K'),e.scale(e.mul(EP,ep('1/a**2')),-1)))
    check('actual_source_elliptic_minus',e.add(e.power(dd,2),ep('2*q**3+z*q/2+K'),e.scale(e.mul(EP,ep('1/a**2')),-1)))
    paq=e.diff(EP,'a')
    check('elliptic_source_Paq_equals_two_asd',e.add(paq,e.scale(e.mul(ep('2*a'),e.mul(ss,dd)),-1),e.scale(e.mul(EP,ep('1/a')),-2)))
    dens=e.add(e.mul(ep('4*q**3'),e.mul(ss,dd)),e.scale(e.mul(paq,e.add(ss,e.scale(dd,-1))),-1),e.mul(ep('4*q**3/a**2'),EP))
    check('actual_elliptic_density_one_twelfth',dens)
    ww=e.mul(ss,dd)
    check('third_quotient_is_endpoint_genus_two',e.add(e.power(ww,2),e.scale(e.power(LL,2),-1),ep('4*q**6'),e.scale(e.mul(e.power(EP,2),ep('1/a**4')),-1),e.mul(ep('2/a**2'),e.mul(EP,LL))))
    result={'status':'passed','count':len(checks),'checks':checks,
        'actual_partial_current':{'Peta':'B theta(eta_H)/(9H)','Qeta':'B theta(eta_z)/(9H)','remainder':'-B theta(J)/(9H^2)'},
        'scope':'Log-free actual rational partial curl, valid for any b-only B commuting T,Dz, including B12. J is explicit and remains unserved. The ambient pole-two remainder is the known corrected source convention, not a new closure. No bounded nonmembership calculation, full primitive or certificate is asserted.'}
    Path(__file__).with_name('source-rational-curl-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
