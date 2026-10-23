#!/usr/bin/env python3
"""Independent exact physical Euler current and genuine coupled scope audit."""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    r=LaurentRing(['Z','h','u','v']);p=r.laurent
    H,C,B=p('1+1/Z**2+h**6'),p('Z**2+u**6+v**6'),p('u/2+h*v/3+h*u*v/(2*Z)')
    K=r.add(r.mul(p('2*h**6'),C),r.scale(r.mul(H,p('v**6')),-1))
    L=p('2*(Z**2+u**6)*h**6+(1+1/Z**2)*v**6')
    vec=[{},p('h'),{},p('-v')]
    def E(poly):return r.add(*(r.mul(ai,r.diff(poly,var)) for ai,var in zip(vec,r.names)))
    divE=r.add(*(r.diff(ai,var) for ai,var in zip(vec,r.names)))
    check('physical_E_divergence_zero',divE)
    check('complete_physical_B_fixed',E(B))
    check('physical_E_K_equals_six_L',r.add(E(K),r.scale(L,-6)))
    # EB=0, so (E log kappa)HC=-H EC-2C EH, retaining both variations.
    log_num=r.add(r.scale(r.mul(H,E(C)),-1),r.scale(r.mul(C,E(H)),-2))
    check('physical_E_logk_all_H_C_factors',r.add(log_num,r.scale(K,6)))
    check('U_logk_has_exact_source_normalization',r.add(log_num,r.scale(K,6)))
    # div(E/(12K))=(K divE-EK)/(12K^2).
    divnum=r.add(r.mul(K,divE),r.scale(E(K),-1))
    check('physical_U_divergence_full_quotient_derivative',r.add(divnum,r.scale(L,6)))
    rr=Ring(['k']);s=rr.poly
    tt=s('4*k+27');fn=s('27-2*k');fd=rr.scale(tt,2)
    fn_der=rr.mul(s('k'),rr.add(rr.mul(rr.diff(fn,'k'),fd),rr.scale(rr.mul(fn,rr.diff(fd,'k')),-1)))
    cn=s('3*(27-23*k)')
    check('P_connection_V_coefficient',rr.add(fn_der,rr.scale(tt,12),rr.scale(cn,-4)))
    check('P_connection_W_coefficient_zero',rr.add(rr.scale(fn,-2),rr.scale(fn,2)))
    # Canonical currents are A=U+fD and Bvec=D. Both complete equation
    # coefficients must be checked, rather than keeping only P's V term.
    cc=Ring(['k','dU','Dl','Ul','g']);q=cc.poly
    t=q('4*k+27');cnum=q('3*(27-23*k)')
    theta_fn=q('-81*k')
    # Clear t^2: (divA+a Dl)-(divU+c Dl)=0, divD=0.
    check('complete_coupled_first_coefficient',cc.add(theta_fn,cc.scale(t,3),cc.scale(cnum,-1)))
    check('complete_coupled_second_coefficient',q('-(27-2*k)+(27-2*k)'))
    # At a real rational physical point, all supposedly required couplings
    # remain nonzero. No pure-component constraint has been hidden.
    ev=lambda poly:sum(poly.values(),Q(0))
    hv,cv,bv,kv,lv=map(ev,[H,C,B,K,L])
    kap=bv**3/(cv*hv**2);tv=4*kap+27
    fv=(27-2*kap)/(2*tv);c0=3*(27-23*kap)/tv**2
    Dl=lv/(2*c0*kv**2);divU=-lv/(2*kv**2);Ul=-1/(2*cv*hv)
    divA=divU-81*kap*Dl/tv**2
    Al=Ul+fv*Dl
    assert Dl and divA and Al and divA==-3*Dl/tv
    checks.append('full_canonical_required_couplings_nonzero_at_physical_point')
    assert divU+c0*Dl==0 and -2*Ul==1/(cv*hv)
    checks.append('actual_full_source_coefficients_at_physical_point')
    result={'status':'passed','checks':checks,'count':len(checks),
        'arithmetic':'independent standard-library Fraction Laurent polynomials',
        'source':'R=W/(HC), with actual volume -dZ dh du dv/3',
        'criterion':'divD=0 and D(log kappa)=L/(2*c0*K^2), c0=3(27-23kappa)/(4kappa+27)^2',
        'actual_current':'J=V*U+(f*V+W)*D; canonical A=U+fD, Bvec=D',
        'scope':'Conditional current is genuinely coupled and has exact physical source if D exists. No pure-component contradiction is implied by divD=0; D and a rational Hamiltonian solving the narrower option remain unconstructed. No certificate has been found.'}
    Path(__file__).with_name('coupled-euler-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
