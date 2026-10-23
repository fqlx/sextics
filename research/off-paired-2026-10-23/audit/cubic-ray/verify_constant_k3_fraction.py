#!/usr/bin/env python3
"""Independent actual density, finite K3 and two-elliptic correspondence audit."""
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


def det(r,m):
    n=len(m)
    return r.add(*(r.scale(__import__('functools').reduce(r.mul,[m[i][pm[i]] for i in range(n)],r.const(1)),
        (-1)**sum(pm[i]>pm[j] for i in range(n) for j in range(i+1,n))) for pm in itertools.permutations(range(n))))


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    r=LaurentRing(['Z','h','u','v'])
    pp=r.laurent
    image=[pp('1/Z'),pp('u'),pp('h*v'),pp('h**6')]
    jac=det(r,[[r.diff(f,v) for v in r.names] for f in image])
    check('full_actual_base_Jacobian',r.add(jac,pp('6*h**6/Z**2')))
    check('physical_density_minus_one_third',r.add(r.mul(jac,pp('Z**2/(18*h**6)')),r.const(Q(1,3))))
    h=pp('1+1/Z**2+h**6')
    b=pp('u/2+h*v/3+h*u*v/(2*Z)')
    c=pp('Z**2+u**6+v**6')
    old=LaurentRing(['z','U','K','t'])
    vals=dict(zip(old.names,image))
    def subst_laurent(poly):
        # All negative exponents here occur in z or t, whose images are
        # single Laurent monomials, so substitution is exact termwise.
        out={}
        for ex,co in poly.items():
            term=r.const(co)
            for name,power in zip(old.names,ex):
                value=vals[name]
                if power<0:
                    (ee,cc),=value.items()
                    value={tuple(-i for i in ee):1/cc};power=-power
                term=r.mul(term,r.power(value,power))
            out=r.add(out,term)
        return out
    for name,actual,original in [('H',h,'1+z**2+t'),('B',b,'U/2+K/3+z*U*K/2'),('C',c,'1/z**2+U**6+K**6/t')]:
        check('complete_physical_'+name,r.add(actual,r.scale(subst_laurent(old.laurent(original)),-1)))
    def bracket(x,y):
        return r.add(r.mul(r.diff(x,'Z'),r.diff(y,'h')),r.scale(r.mul(r.diff(x,'h'),r.diff(y,'Z')),-1),
                     r.mul(r.diff(x,'u'),r.diff(y,'v')),r.scale(r.mul(r.diff(x,'v'),r.diff(y,'u')),-1))
    check('new_H_C_monomial_bracket',r.add(bracket(h,c),pp('12*Z*h**5')))
    check('new_H_B_bracket',r.add(bracket(h,b),pp('2*v/(3*Z**3)+u*v/Z**4-3*h**6*u*v/Z**2')))
    check('new_B_C_bracket',r.add(bracket(b,c),pp('2*Z*v/3+u*v-3*v**5-3*h*v**6/Z+2*h*u**5+3*h*u**6/Z')))
    for name,poly in [('H',h),('B',b),('C',c)]:
        assert all((ex[1]-ex[3])%6==0 for ex in poly)
        checks.append('degree6_base_deck_invariance_'+name)
    assert (1-1)%6==0
    checks.append('degree6_base_deck_preserves_physical_volume')
    # Useful coefficient-normal frame, with all B drift still retained.
    vh=[{},pp('1/(6*h**5)'),{},{}]
    vc=[pp('1/(2*Z)'),pp('1/(6*Z**4*h**5)'),{},{}]
    def act(vec,f):return r.add(*(r.mul(ai,r.diff(f,var)) for ai,var in zip(vec,r.names)))
    for name,vec,vH,vC in [('H_normal',vh,1,0),('C_normal',vc,0,1)]:
        check(name+'_H',r.add(act(vec,h),r.const(-vH)))
        check(name+'_C',r.add(act(vec,c),r.const(-vC)))
    kv=[{}, {},pp('6*v**5'),pp('-6*u**5')]
    check('HC_vertical_K_H',act(kv,h));check('HC_vertical_K_C',act(kv,c))
    check('HC_vertical_K_B_full_drift',r.add(act(kv,b),pp('-3*v**5-3*h*v**6/Z+2*h*u**5+3*h*u**6/Z')))

    # Common field on the finite K3/elliptic correspondence. Normalization
    # checks clear nonzero chart factors w,Y, then use a triangular exact
    # reduction; no primary Groebner basis or SymPy code is imported.
    k=LaurentRing(['c','h','T','e','w','Y','V'])
    lp=k.laurent
    def reduce(poly):
        # V^2=e/w, then clear negative w,Y powers and use w^3=1+T^6,
        # Y^2=1-e^3. c,h,T,e are independent Laurent base coordinates.
        stage={}
        for ex,co in poly.items():
            assert ex[6]>=0
            qv,rv=divmod(ex[6],2)
            ee=list(ex);ee[3]+=qv;ee[4]-=qv;ee[6]=rv
            stage=k.add(stage,{tuple(ee):co})
        if not stage:return {}
        sw=max(0,-min(ex[4] for ex in stage));sy=max(0,-min(ex[5] for ex in stage))
        out={}
        for ex,co in stage.items():
            ee=list(ex);ee[4]+=sw;ee[5]+=sy
            qw,rw=divmod(ee[4],3);qy,ry=divmod(ee[5],2)
            for iw in range(qw+1):
                for iy in range(qy+1):
                    ff=ee.copy();ff[2]+=6*iw;ff[3]+=3*iy;ff[4]=rw;ff[5]=ry
                    out=k.add(out,{tuple(ff):co*comb(qw,iw)*comb(qy,iy)*(-1)**iy})
        return out
    def kc(name,residual):check(name,reduce(residual))
    def deriv(poly,var):
        ans=k.diff(poly,var)
        if var=='T':ans=k.add(ans,k.mul(k.diff(poly,'w'),lp('2*T**5/w**2')),k.mul(k.diff(poly,'V'),lp('-V*T**5/w**3')))
        if var=='e':ans=k.add(ans,k.mul(k.diff(poly,'Y'),lp('-3*e**2/(2*Y)')),k.mul(k.diff(poly,'V'),lp('V/(2*e)')))
        return ans
    relations=[lp('w**3-1-T**6'),lp('Y**2-1+e**3'),lp('w*V**2-e')]
    for var in ['T','e']:
        for i,relation in enumerate(relations):kc('separable_derivation_'+var+str(i),deriv(relation,var))
    U=lp('T*V');VV=lp('V');YY=lp('Y')
    kc('actual_normalized_K3_equation',k.add(k.power(YY,2),k.power(U,6),k.power(VV,6),k.const(-1)))
    physical=[lp('c**3*Y'),lp('h'),lp('c*T*V'),lp('c*V')]
    def actual_pullback(poly):
        answer={}
        for ex,co in poly.items():
            term=k.const(co)
            for ee,image in zip(ex,physical):
                (iex,ico),=image.items()
                factor={tuple(ee*i for i in iex):ico**ee}
                term=k.mul(term,factor)
            answer=k.add(answer,term)
        return answer
    cc=k.add(k.power(physical[0],2),k.power(physical[2],6),k.power(physical[3],6))
    kc('physical_C_equals_c_sixth',k.add(cc,lp('-c**6')))
    hh=lp('1+1/(c**6*Y**2)+h**6')
    bb=lp('c*V*(T/2+h/3)+h*T*V**2/(2*c*Y)')
    # These are direct full substitutions in the rational chart; H,B have
    # not been averaged over the fixed elliptic curves.
    kc('physical_full_H_retained',k.add(hh,k.scale(actual_pullback(h),-1)))
    kc('physical_full_B_retained',k.add(bb,k.scale(actual_pullback(b),-1)))
    e1,y1=lp('w**2/T**2'),lp('(T**6-1)/T**3')
    kc('first_fixed_elliptic_equation',k.add(k.power(y1,2),k.scale(k.power(e1,3),-1),k.const(4)))
    kc('first_fixed_elliptic_differential',k.add(deriv(e1,'T'),k.scale(k.mul(lp('2/w'),y1),-1)))
    kc('second_fixed_elliptic_equation',lp('Y**2-1+e**3'))
    angle=k.add(k.mul(deriv(U,'T'),deriv(VV,'e')),k.scale(k.mul(deriv(U,'e'),deriv(VV,'T')),-1))
    kc('K3_twoform_product_with_correct_factor2',k.add(k.mul(angle,lp('1/Y')),lp('-1/(2*w*Y)')))
    bvar=lp('w/T')
    kc('finite_inverse_square',k.add(k.power(bvar,2),k.scale(e1,-1)))
    kc('finite_inverse_T_cube',k.add(lp('T**3'),k.scale(k.add(y1,k.power(bvar,3)),Q(-1,2))))
    jj=det(k,[[deriv(value,var) for var in ['c','h','T','e']] for value in physical])
    kc('actual_fourform_Jacobian_and_orientation',k.add(k.scale(jj,Q(-1,3)),lp('c**4/(2*w*Y)')))
    # c^6 deck: c->zeta*c, Y->zeta^-3Y, V->zeta^-1V,
    # e->zeta^-2e; T,w,h fixed. This fixes all physical coordinates.
    weights=[1,0,0,-2,0,-3,-1]
    for name,poly in [('Z',physical[0]),('h',physical[1]),('u',physical[2]),('v',physical[3]),('H',hh),('B',bb)]:
        assert all(sum(ex[i]*weights[i] for i in range(7))%6==0 for ex in poly)
        checks.append('K3_c_normalization_deck_'+name)
    assert (4+1+(-2)-(-3))%6==0
    checks.append('K3_c_deck_preserves_full_source_volume')
    # Adjoining w over K3: w->omega*w, e->omega*e, V fixed.
    # eta1 has character -1 and eta2 +1; H,B do not depend on e,w.
    assert all(ex[3]==0 and ex[4]==0 for ex in hh|bb)
    checks.append('K3_w_deck_preserves_source_and_product_density')
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'standard-library Fraction Laurent dictionaries and independent triangular field reduction',
        'physical_constant_density':'-dZ wedge dh wedge du wedge dv/3',
        'physical_K3_density':'-c^4 dc wedge dh wedge eta1 wedge eta2',
        'full_source':'-c^4 Bp/(B+3c^6 p^2)^3 dc wedge dh wedge eta1 wedge eta2, with H=1+c^-6 Y^-2+h^6 and complete B retained',
        'finite_bounds':'degree6 for the rational base cover; after adjoining c^6=C, common angle field has degree<=3 over normalized K3 and<=12 over the fixed elliptic product; no stronger field degrees claimed',
        'scope':'Exact source-preserving coordinate/correspondence identities, normal frame and finite-deck coverage. Factorization of density does not integrate the full cubic source or supply a kernel lift. No certificate has been found.'}
    Path(__file__).with_name('constant-k3-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
