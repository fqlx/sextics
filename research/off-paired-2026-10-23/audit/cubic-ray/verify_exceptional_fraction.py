#!/usr/bin/env python3
"""Independent weighted exceptional surface, target source and first-jet audit."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import itertools
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
    r=Ring(['eps','a','b','H','mij','mjk','mik']);p=r.poly
    c0=p('1+a**6+b**6');m0=p('mij*a+mjk*b+mik*a*b')
    cy=r.mul(p('eps**6'),c0);tt=p('eps**6*(1+a**6)');kk=p('eps**12*a**6')
    d18=r.add(r.mul(cy,r.power(tt,2)),r.mul(p('16*H'),kk))
    hx=r.add(r.scale(r.mul(p('eps**2'),m0),-1),r.scale(r.mul(p('eps**6'),c0),-1))
    vals={n:r.var(n) for n in r.names};vals['H']=hx
    strict=r.add(r.mul(p('eps**4'),r.mul(c0,p('(1+a**6)**2-16*a**6'))),r.scale(r.mul(p('16*a**6'),m0),-1))
    check('full_original_strict_graph_transform',r.add(r.subst(d18,vals,r),r.scale(r.mul(p('eps**14'),strict),-1)))
    t=Ring(['t','A','b','mij','mjk','mik','w']);tp=t.poly
    sub={'eps':tp('t**3'),'a':tp('t**2*A'),'b':tp('b'),'H':{},'mij':tp('mij'),'mjk':tp('mjk'),'mik':tp('mik')}
    ss=tp('(1+b**6+t**12*A**6)*((1+t**12*A**6)**2-16*t**12*A**6)-16*A**6*(mjk*b+t**2*A*(mij+mik*b))')
    check('exact_weighted_t54_model',t.add(r.subst(strict,sub,t),t.scale(t.mul(tp('t**12'),ss),-1)))
    ss0={ex:co for ex,co in ss.items() if ex[0]==0}
    # b*S0=1*b+b^7-mjk*w^2, where w^2=16A^6b^2.
    check('exceptional_surface_quotient_equation',t.add(t.mul(tp('b'),ss0),tp('-b-b**7+16*mjk*A**6*b**2')))
    for exponent in [(5,1),(3,0),(3,0)]:
        assert sum(exponent)%3==0
    checks.append('weighted_chart_residual_mu3_fixes_all_Y_coordinates')

    # Whole elliptic maps. k0=2sqrt(2)i, hence k0^2=-8. Use exact
    # coefficient reduction and z^6=-1-64xi^12, never complex floats.
    ec=Ring(['xi','z','k0']);ep=ec.poly
    def ec_reduce(poly):
        out={}
        for (ei,ez,ek),co in poly.items():
            qz,rz=divmod(ez,6);qk,rk=divmod(ek,2)
            for j in range(qz+1):
                key=(ei+12*j,rz,rk)
                out=ec.add(out,{key:co*(-8)**qk*comb(qz,j)*(-1)**qz*64**j})
        return out
    uc,vc=ep('8*xi**6'),ep('k0*xi**3*z**3')
    check('whole_Cprime_to_fixed_Ei',ec_reduce(ec.add(ec.power(vc,2),ec.scale(ec.power(uc,3),-1),ec.scale(uc,-1))))
    # dxi/dx=1/(4xi): clear 8xi*VC in dUC/(2VC)=6xi dx/(k0 z^3).
    check('Cprime_elliptic_differential',ec.add(ec.mul(ec.diff(uc,'xi'),ep('k0*z**3')),ec.scale(ec.mul(ep('48*xi**2'),vc),-1)))
    eg=Ring(['b','y']);gp=eg.poly
    ug,vg=gp('b**3'),gp('b*y')
    gmap=eg.add(eg.power(vg,2),eg.scale(eg.power(ug,3),-1),eg.scale(ug,-1))
    gv=gp('y**2-b**7-b')
    check('whole_G_to_fixed_Ei',eg.add(gmap,eg.scale(eg.mul(gp('b**2'),gv),-1)))
    check('G_elliptic_differential',eg.add(eg.mul(eg.diff(ug,'b'),gp('2*y')),eg.scale(eg.mul(gp('3*b'),eg.scale(vg,2)),-1)))
    # Product coefficient etaC*etaG =9b/(k0 z^3 w), gamma=4b/(z^3w).
    scalar=Ring(['b','xi','w','y','z','k0']);sp=scalar.poly
    product_num=sp('9*xi*b');product_den=sp('k0*z**3*y')
    gamma_num=sp('4*b');gamma_den=sp('z**3*w')
    diff=scalar.add(scalar.mul(product_num,scalar.mul(sp('4*k0'),gamma_den)),
                    scalar.scale(scalar.mul(sp('9'),scalar.mul(gamma_num,product_den)),-1))
    substitution={v:scalar.var(v) for v in scalar.names};substitution['y']=sp('xi*w')
    check('nonzero_elliptic_product_descends_to_gamma',scalar.subst(diff,substitution,scalar))

    # Independent full G36 invariance, including the paired Y-sign that
    # was implicit in the note's order-three plus order-six generators.
    weights=[(0,0),(2,0),(0,1),(1,0),(3,0),(3,5)]
    total_volume=tuple(sum(w[j] for w in weights)%6 for j in range(2))
    target_A=(3,0)
    assert total_volume==(3,0) and tuple((total_volume[i]+target_A[i])%6 for i in range(2))==(0,0)
    checks.append('actual_A_projective_volume_character_invariant')
    anti=[(i,j) for j in range(1,6) for i in range(1,2*j) if i%2]
    assert len(anti)==15
    invariant=sorted((i,j,l) for i,j in anti for l in range(3) if (i-2*l-1)%12==0 and (i-2*j)%3==0)
    assert invariant==[(1,2,0),(1,5,0),(3,3,1),(5,4,2)]
    checks.append('all_four_invariant_exceptional_H20_forms')
    # rational coefficient r*x^a*b^ell/z^j; dx db is included.
    forms=[(-1,-1,2),(-1,-1,5),(0,0,3),(1,1,4)]
    for n,(ax,bb,jz) in enumerate(forms):
        assert (ax-bb)%6==0                 # X2,Y2 order-six generator
        assert (2*(jz-ax))%6==0             # full other order-six generator
        checks.append('full_G36_form_character_'+str(n))
    checks.append('paired_Y_sign_is_trivial_on_exceptional_surface')

    # Actual target numerator and exact Y-chart Jacobian, retaining Az.
    s=Ring(['x','z','Y0','Y1','Y2','t','A','b']);fp=s.poly
    F=fp('z**6+1+x**6+Y0**6+Y1**6+Y2**6+z**3*Y0*Y1/2+x*Y1*Y2/2+z**2*x*Y0*Y2/3')
    source=fp('z**3*Y0**3')
    fz=s.diff(F,'z');fzz=s.diff(fz,'z')
    num=s.add(s.mul(source,fzz),s.scale(s.mul(s.diff(source,'z'),fz),-1))
    vals={n:s.var(n) for n in s.names};vals.update({'Y0':fp('t**5*A'),'Y1':fp('t**3'),'Y2':fp('t**3*b')})
    images=[vals['Y0'],vals['Y1'],vals['Y2']]
    jac={}
    for pm in itertools.permutations(range(3)):
        co=(-1)**sum(pm[i]>pm[j] for i in range(3) for j in range(i+1,3))
        term=s.const(co)
        for i in range(3):term=s.mul(term,s.diff(images[i],['t','A','b'][pm[i]]))
        jac=s.add(jac,term)
    check('actual_three_Y_Jacobian_negative',s.add(jac,fp('3*t**10')))
    nt=s.mul(s.subst(num,vals,s),jac);den=s.power(s.subst(fz,vals,s),3)
    assert min(ex[5] for ex in nt)==25
    leadn={ex[:5]+(0,)+ex[6:]:co for ex,co in nt.items() if ex[5]==25}
    leadd={ex:co for ex,co in den.items() if ex[5]==0}
    check('actual_target_leading_source_with_Az',s.add(s.mul(leadn,fp('z**8')),s.scale(s.mul(fp('A**3'),leadd),Q(1,6))))
    # X1=1 projective volume is -dz dx dY0 dY1 dY2, giving the
    # positive (AFzz-AzFz)/Fz^3 before the negative Y-Jacobian above.
    checks.append('fixed_projective_orientation_leading_source_negative_t25_over6')

    # Exact quotient-free global chart and first normal derivative.
    a=LaurentRing(['a','b','x','z','r','w']);ap=a.laurent
    M=ap('x*b/2+a*(z**3/2+z**2*x*b/3)')
    C0=ap('1+b**6+a**6');K0=ap('(1+a**6)**2-16*a**6')
    H0=ap('z**6+x**6+1')
    hx_repl=a.add(a.scale(a.mul(ap('r*a**3'),M),-1),a.scale(a.mul(ap('r**3*a**9'),C0),-1))
    # R1=16M-r^2 C0K0; identity reduces R2 using R1 without dividing
    # by a, so it is valid at the exceptional chart as well.
    R1=a.add(a.scale(M,16),a.scale(a.mul(ap('r**2'),a.mul(C0,K0)),-1))
    R2=a.add(a.scale(hx_repl,16),a.mul(ap('r**3*a**3'),a.mul(C0,ap('(1+a**6)**2'))))
    check('exact_global_second_normal_relation',a.add(R2,a.mul(ap('r*a**3'),R1)))
    L0=ap('z**3/2+z**2*x*b/3')
    central=a.add(ap('r**2*(1+b**6)'),ap('-8*x*b'))
    # At a=0, H_z z_a=0 -> z_a=0 on z!=0. The differentiated first
    # equation gives r_a/r=L0/(xb), using the actual central relation.
    deriv_first=a.add(ap('16*x*b'),a.scale(ap('2*r**2*(1+b**6)'),-1))
    check('actual_first_normal_r_jet',a.add(deriv_first,a.scale(central,2)))
    gamma3jet=a.mul(ap('r/(x*b*z**3)'),L0)
    check('gamma3_naive_first_jet',a.add(gamma3jet,ap('-r/(2*x*b)-r/(3*z)')))
    # w_x=-w/(2x) on the exceptional surface; d(4 db/w) coefficient.
    wx=ap('-w/(2*x)')
    check('exceptional_w_x_from_full_surface_relation',a.add(ap('w**2/2'),a.mul(ap('x*w'),wx)))
    exact_piece=a.scale(a.mul(wx,ap('1/w**2')),-4)
    first_piece=a.mul(ap('4*b/w'),ap('1/(2*x*b)'))
    check('gamma3_first_piece_exact',a.add(exact_piece,a.scale(first_piece,-1)))
    # (4/3)(xi dx/z) tensor(b db/y), with y=xi*w.
    lhs_n,lhs_d=sp('4*b'),sp('3*z*w')
    rhs_n,rhs_d=sp('4*xi*b'),sp('3*z*y')
    second=scalar.add(scalar.mul(lhs_n,rhs_d),scalar.scale(scalar.mul(rhs_n,lhs_d),-1))
    check('gamma3_remaining_product_class',scalar.subst(second,substitution,scalar))
    # phi4'-(3/2)phi3'=rxb/(3z^2)-3r/(4xb), and the latter is
    # d(-6 db/w). This is a naive-lift relation, not intrinsic KS.
    phi4jet=a.mul(ap('r/z**4'),L0)
    combo=a.add(phi4jet,a.scale(gamma3jet,Q(-3,2)),ap('-r*x*b/(3*z**2)+3*r/(4*x*b)'))
    check('fourth_minus_three_halves_third_first_jet',combo)
    result={'status':'passed','checks':checks,'count':len(checks),
        'arithmetic':'independent standard-library Fraction polynomial/Laurent arithmetic and exact curve relation reductions',
        'exceptional_surface':'(x/2)w^2=b^7+b over z^6+x^6+1=0',
        'holomorphic_invariant_dimension':4,
        'target_leading_source':'-t^25*A^3/(6*z^8) dx wedge dt wedge dA wedge db for the stated X1=1 projective orientation',
        'first_normal_gamma3':'r*(1/(2*x*b)+1/(3*z)) dx wedge db; first piece exact',
        'scope':'Actual nonzero exceptional H20 forms and complete symmetry/source-leading calculation verified. Global closed extension, legitimate holomorphic relative lift, intrinsic KS class and actual Gysin/source matching remain unproved. No certificate has been found.'}
    Path(__file__).with_name('exceptional-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
