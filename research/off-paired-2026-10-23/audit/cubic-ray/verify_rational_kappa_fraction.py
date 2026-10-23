#!/usr/bin/env python3
"""Independent rational S3 kappa cover and fixed-elliptic bridge audit."""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing
from verify_elliptic_cover_fraction import EllipticRing


class ZetaRing(LaurentRing):
    def __init__(self):super().__init__(['q','H','B','zeta'])
    def reduce(self,poly):
        out={}
        for ex,co in poly.items():
            z=ex[-1]%3;stem=ex[:-1]
            for iz,factor in ([(0,1)] if z==0 else [(1,1)] if z==1 else [(0,-1),(1,-1)]):
                key=stem+(iz,)
                out[key]=out.get(key,Q(0))+factor*co
                if not out[key]:del out[key]
        return out
    def mul(self,a,b):return self.reduce(super().mul(a,b))
    def cycle(self,poly):return self.reduce({ex[:-1]+(ex[-1]+ex[0],):co for ex,co in poly.items()})
    def invert_q(self,poly):return {(-ex[0],)+ex[1:]:co for ex,co in poly.items()}


class BridgeRing(Ring):
    def __init__(self):super().__init__(['Y','a','b'])
    def reduce(self,poly):
        out={}
        for (ey,ea,eb),co in poly.items():
            key=(ey,ea%2,eb%2)
            out[key]=out.get(key,Q(0))+co*(-16)**(ea//2)*48**(eb//2)
            if not out[key]:del out[key]
        return out
    def mul(self,a,b):return self.reduce(super().mul(a,b))


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    r=ZetaRing();p=r.poly
    kn,kd=p('-27*q**3'),p('(q**3+1)**2')
    fn,fd=p('q**2-q+1'),p('3*(q**2+q+1)')
    vn,vd=p('-2*q'),fd
    wn,wd=p('q*(q+1)**2*(q**2-q+1)'),p('9*(q**2+q+1)**3')
    an=r.add(r.scale(kn,4),r.scale(kd,27))
    # Canonical cubic polynomial for F, denominator kd*fd^3.
    poly=r.add(r.mul(an,r.power(fn,3)),r.scale(r.mul(an,r.mul(r.power(fn,2),fd)),-1),
               r.mul(r.scale(kd,9),r.mul(fn,r.power(fd,2))),r.scale(r.mul(kd,r.power(fd,3)),-1))
    check('canonical_F_cubic',poly)
    check('V_equals_F_minus_one_third',r.add(r.mul(vn,fd),r.scale(r.mul(fn,vd),-1),r.scale(r.mul(vd,fd),Q(1,3))))
    dk=r.add(r.mul(r.diff(kn,'q'),kd),r.scale(r.mul(kn,r.diff(kd,'q')),-1))
    dv=r.add(r.mul(r.diff(vn,'q'),vd),r.scale(r.mul(vn,r.diff(vd,'q')),-1))
    dw=r.add(r.mul(r.diff(wn,'q'),wd),r.scale(r.mul(wn,r.diff(wd,'q')),-1))
    check('theta_V_equals_minus_two_W',r.add(r.mul(kn,r.mul(kd,r.mul(dv,wd))),r.scale(r.mul(wn,r.mul(dk,r.power(vd,2))),2)))
    left=r.mul(kn,r.mul(kd,r.mul(dw,r.mul(an,r.mul(vd,wd)))))
    right=r.mul(r.add(r.mul(p('3'),r.mul(vn,r.mul(kd,wd))),
                     r.mul(r.add(r.scale(kd,27),r.scale(kn,-2)),r.mul(wn,vd))),
                     r.mul(dk,r.power(wd,2)))
    check('theta_W_full_canonical_equation',r.add(left,r.scale(right,-1)))
    for name,num,den in [('kappa',kn,kd),('F',fn,fd),('W',wn,wd)]:
        check('inversion_fixes_'+name,r.add(r.mul(r.invert_q(num),den),r.scale(r.mul(num,r.invert_q(den)),-1)))
    check('cyclic_fixes_kappa',r.add(r.mul(r.cycle(kn),kd),r.scale(r.mul(kn,r.cycle(kd)),-1)))
    for name,num,den,target in [('V',vn,vd,0),('W',wn,wd,0),('F',fn,fd,1)]:
        ns=[num,r.cycle(num),r.cycle(r.cycle(num))]
        ds=[den,r.cycle(den),r.cycle(r.cycle(den))]
        common=r.mul(ds[0],r.mul(ds[1],ds[2]))
        trace=r.add(*(r.mul(ns[i],r.mul(ds[(i+1)%3],ds[(i+2)%3])) for i in range(3)),r.scale(common,-target))
        check('full_cyclic_trace_'+name,trace)
    # Actual C and cubic root p, with H,B kept physically variable.
    cn,cd=p('-B**3*(1+q**3)**2'),p('27*H**2*q**3')
    pn,pd=p('3*H*q'),p('B*(q**2-q+1)')
    check('actual_physical_cubic',r.add(r.mul(cn,r.power(pn,3)),r.mul(p('B'),r.mul(pn,r.mul(cd,r.power(pd,2)))),r.mul(p('H'),r.mul(cd,r.power(pd,3)))))
    gn=r.add(r.mul(p('B'),r.mul(cd,r.power(pd,2))),r.mul(p('3'),r.mul(cn,r.power(pn,2))))
    gd=r.mul(cd,r.power(pd,2))
    check('F_actual_source_binding',r.add(r.mul(fn,r.mul(pn,gn)),r.mul(fd,r.mul(p('H'),r.mul(cd,r.power(pd,3))))))
    check('W_actual_source_binding',r.add(r.mul(wn,r.mul(cd,r.mul(pd,r.power(gn,3)))),
          r.scale(r.mul(wd,r.mul(cn,r.mul(p('H*B'),r.mul(pn,r.power(gd,3))))),-1)))

    st=Ring(['S','T','c'])
    kk=st.poly('S**2+S*T+T**2')
    hm=st.poly('S**3+T**3')
    minus=st.poly('S**2-S*T+T**2')
    check('Cardano_ratio_kappa_normalization',st.add(st.power(st.poly('-3*c*S*T'),3),st.poly('27*c**3*S**3*T**3')))
    check('Cardano_ratio_F_normalization',st.add(hm,st.scale(st.mul(st.poly('S+T'),minus),-1)))
    check('Cardano_ratio_W_normalization',st.add(st.mul(st.poly('S*T*(S+T)'),hm),
          st.scale(st.mul(st.poly('S*T*(S+T)**2'),minus),-1)))

    # Branch indices: q=0,infinity ->0 with index3; q^3=1 ->-27/4
    # index2; q^3=-1 ->infinity with index2. Degree6 and these exhaust
    # 2*degree-2=10 ramification. The finite derivative is checked exactly.
    check('kappa_derivative_factorization',r.add(dk,r.scale(r.mul(p('-81*q**2*(1-q**3)'),p('q**3+1')),-1)))
    check('minus_27_over_4_branch_factor',r.add(r.scale(kn,4),r.scale(kd,27),p('-27*(q**3-1)**2')))
    assert 2*(3-1)+3*(2-1)+3*(2-1)==2*6-2
    checks.append('degree6_full_S3_branch_signature_3_2_2')

    # Bridge to the independently audited fixed elliptic cover. a=4i,
    # b=4sqrt(3), q=(b-Y)/(b+Y). This is the root-normalization quotient.
    e=EllipticRing();ep=e.laurent
    xt=ep('-32/X**2-2*a*Y/X**2')
    yt=e.add(ep('-a'),e.scale(e.mul(ep('(Y-a)/X'),xt),-1))
    check('elliptic_translation_Y_mobius',e.add(e.mul(yt,ep('Y+a')),e.scale(ep('a*(Y-3*a)'),-1)))
    b=BridgeRing();bp=b.poly
    qn,qd=bp('b-Y'),bp('b+Y')
    fbn=b.add(b.power(qn,2),b.scale(b.mul(qn,qd),-1),b.power(qd,2))
    fbd=b.scale(b.add(b.power(qn,2),b.mul(qn,qd),b.power(qd,2)),3)
    check('elliptic_to_rational_F_bridge',b.add(b.mul(fbn,bp('Y**2+144')),b.scale(b.mul(fbd,bp('Y**2+16')),-1)))
    wbn=b.mul(qn,b.mul(qd,b.mul(b.power(b.add(qn,qd),2),fbn)))
    wbd=b.scale(b.power(b.add(b.power(qn,2),b.mul(qn,qd),b.power(qd,2)),3),9)
    check('elliptic_to_rational_W_bridge',b.add(b.mul(wbn,bp('(Y**2+144)**3')),
        b.mul(wbd,bp('64*(Y**2+16)*(Y**2-48)'))))
    kbn=b.scale(b.mul(b.power(qn,3),b.power(qd,3)),-27)
    kbd=b.power(b.add(b.power(qn,3),b.power(qd,3)),2)
    check('elliptic_j_cubed_kappa_bridge',b.add(b.mul(kbn,bp('64*(Y**2+16)**2')),
        b.scale(b.mul(kbd,bp('(Y**2-48)**3')),-1)))
    zeta=bp('-1/2+a*b/32')
    check('bridge_primitive_cube_root',b.add(b.power(zeta,2),zeta,b.const(1)))
    ty_n,ty_d=bp('a*(Y-3*a)'),bp('Y+a')
    tq_n=b.add(b.mul(bp('b'),ty_d),b.scale(ty_n,-1))
    tq_d=b.add(b.mul(bp('b'),ty_d),ty_n)
    check('elliptic_T_is_q_times_zeta',b.add(b.mul(tq_n,qd),b.scale(b.mul(zeta,b.mul(qn,tq_d)),-1)))
    result={'status':'passed','checks':checks,'count':len(checks),
        'arithmetic':'standard-library Fraction quotient polynomial/Laurent dictionaries; zeta^2+zeta+1=0, a^2=-16,b^2=48',
        'kappa':'-27*q^3/(q^3+1)^2','q':'S/T',
        'source':'W=H*C*R=q*(q+1)^2*(q^2-q+1)/(9*(q^2+q+1)^3)',
        'elliptic_bridge':'q=(4sqrt(3)-Y)/(4sqrt(3)+Y); elliptic deck translation acts q -> zeta*q with zeta=(-1+i*sqrt(3))/2',
        'scope':'Full rational S3 cover of kappa and actual source binding checked. The fixed elliptic cover over j is its cube-root-normalization pullback, not the same base parameter. No physical primitive follows from either normalization; no certificate has been found.'}
    Path(__file__).with_name('rational-kappa-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
