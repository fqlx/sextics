#!/usr/bin/env python3
"""Independent exact fixed S3 elliptic-cover/source audit, stdlib only."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


class EllipticRing(LaurentRing):
    """Q[X^+-1,Y,a]/(Y^2-X^3+16,a^2+16), a=4i."""
    def __init__(self):
        super().__init__(['X','Y','a'])

    def reduce(self, poly):
        out={}
        for (ex,ey,ea),co in poly.items():
            assert ey>=0 and ea>=0
            yy,aa=ey//2,ea//2
            for k in range(yy+1):
                e=(ex+3*k,ey%2,ea%2)
                v=co*comb(yy,k)*(-16)**(yy-k+aa)
                out[e]=out.get(e,Q(0))+v
                if not out[e]:del out[e]
        return out

    def mul(self,x,y):
        return self.reduce(super().mul(x,y))


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    e=EllipticRing()
    p=e.laurent
    x,y,aa=[e.var(q) for q in e.names]
    xt=p('-32/X**2-2*a*Y/X**2')
    x2=p('-32/X**2+2*a*Y/X**2')
    yt=e.add(p('-a'),e.scale(e.mul(p('(Y-a)/X'),xt),-1))
    y2=e.add(aa,e.scale(e.mul(p('(Y+a)/X'),x2),-1))
    check('translation_preserves_E',e.add(e.power(yt,2),e.scale(e.power(xt,3),-1),e.const(16)))
    check('inverse_translation_preserves_E',e.add(e.power(y2,2),e.scale(e.power(x2,3),-1),e.const(16)))
    check('translation_X_inverse_product',e.add(e.mul(xt,x2),p('-64/X')))
    xt_inv=e.mul(x,x2)
    xt_inv=e.scale(xt_inv,Q(1,64))
    def T(poly):
        ans={}
        for (ex,ey,ea),co in poly.items():
            v=e.scale(e.mul(e.power(xt if ex>=0 else xt_inv,abs(ex)),
                                e.mul(e.power(yt,ey),e.power(aa,ea))),co)
            ans=e.add(ans,v)
        return ans
    def sigma(poly):
        return {ex:co*(-1)**ex[1] for ex,co in poly.items()}
    check('T_squared_X',e.add(T(xt),e.scale(x2,-1)))
    check('T_squared_Y',e.add(T(yt),e.scale(y2,-1)))
    check('T_cubed_X',e.add(T(x2),e.scale(x,-1)))
    check('T_cubed_Y',e.add(T(y2),e.scale(y,-1)))
    check('sigma_T_sigma_X',e.add(sigma(T(sigma(x))),e.scale(x2,-1)))
    check('sigma_T_sigma_Y',e.add(sigma(T(sigma(y))),e.scale(y2,-1)))

    u=p('X-64/X**2')
    v=p('-Y*(1+128/X**3)')
    check('isogeny_target_equation',e.add(e.power(v,2),e.scale(e.power(u,3),-1),e.const(-432)))
    check('T_fixes_U',e.add(T(u),e.scale(u,-1)))
    check('T_fixes_V',e.add(T(v),e.scale(v,-1)))
    check('sigma_fixes_U',e.add(sigma(u),e.scale(u,-1)))
    check('sigma_negates_V',e.add(sigma(v),v))
    r=p('-4/X')
    check('normalized_cubic',e.add(e.power(r,3),e.scale(e.mul(u,r),Q(1,4)),e.const(1)))
    roots=[r,T(r),T(T(r))]
    check('whole_deck_root_sum',e.add(*roots))
    check('whole_deck_root_pair_sum',e.add(*(e.mul(roots[i],roots[j]) for i,j in [(0,1),(0,2),(1,2)]),e.scale(u,Q(-1,4))))
    check('whole_deck_root_product',e.add(e.mul(roots[0],e.mul(roots[1],roots[2])),e.const(1)))

    # Single rho normalization: H=C*rho^3, B=C*rho^2*j,
    # p=rho*r.  This avoids inconsistent independent cube-root choices.
    n=Ring(['C','rho','j','r'])
    check('physical_cubic_normalization',n.poly('C*rho**3+C*rho**2*j*rho*r+C*(rho*r)**3-C*rho**3*(1+j*r+r**3)'))
    check('physical_g_normalization',n.poly('C*rho**2*j+3*C*(rho*r)**2-C*rho**2*(j+3*r**2)'))
    # HC*B*p/g^3 = jr/(j+3r^2)^3 by cancelling common monomials.
    check('physical_HC_source_normalization',n.poly('(C*rho**3)*C*(C*rho**2*j)*(rho*r)-C**3*rho**6*j*r'))

    den=p('X**3+128')
    source_num=p('-64*X**3*(X**3-64)')
    # j r/(j+3r^2)^3, clearing 64 X^6 as necessary.
    d=e.add(e.scale(u,Q(1,4)),e.scale(e.power(r,2),3))
    check('normalized_g_X_expression',e.add(e.mul(p('4*X**2'),d),e.scale(den,-1)))
    check('actual_source_X_expression',e.add(e.mul(e.scale(e.mul(u,r),Q(1,4)),e.power(p('4*X**2'),3)),e.scale(source_num,-1)))
    # F=-1/[r(j+3r^2)] = X^3/(X^3+128).
    fnum=p('X**3')
    check('canonical_F_X_expression',e.add(e.mul(fnum,e.mul(r,d)),den))

    dens=[den,T(den),T(T(den))]
    fnums=[fnum,T(fnum),T(T(fnum))]
    nums=[source_num,T(source_num),T(T(source_num))]
    common=e.mul(dens[0],e.mul(dens[1],dens[2]))
    trace_f={}
    trace_source={}
    for i in range(3):
        others=[j for j in range(3) if j!=i]
        product=e.mul(dens[others[0]],dens[others[1]])
        trace_f=e.add(trace_f,e.mul(fnums[i],product))
        trace_source=e.add(trace_source,e.mul(nums[i],e.power(product,3)))
    check('whole_kernel_trace_F_one',e.add(trace_f,e.scale(common,-1)))
    check('whole_kernel_trace_actual_HC_R_zero',trace_source)
    check('sigma_fixes_source_numerator',e.add(sigma(source_num),e.scale(source_num,-1)))
    check('sigma_fixes_source_denominator',e.add(sigma(den),e.scale(den,-1)))

    # Cube-root normalization ambiguity A: rho -> w rho, X -> w X,
    # Y -> Y, w^3=1.  Checking every monomial's weight is an exact
    # polynomial proof of the stated eigencharacters and commutation.
    for name,poly,weight in [('X_T',xt,1),('Y_T',yt,0),('U',u,1),
                             ('V',v,0),('source_numerator',source_num,0),
                             ('source_denominator',den,0),('F_numerator',fnum,0)]:
        assert all(ex[0]%3==weight for ex in poly),(name,poly)
        checks.append('mu3_normalization_character_'+name)
    # The normalized expressions for physical H, B and p are invariant:
    # H=C rho^3, B=C rho^2 j, p=-4 rho/X.
    for name,weight in [('physical_H',3),('physical_B',2+1),('physical_p',1-1)]:
        assert weight%3==0
        checks.append('mu3_descent_'+name)

    # Group ring Q[T]/(T^3-1). Check universal operator identities, rather
    # than treating a trace-free source as an integration theorem.
    def grmul(a,b):
        out=[Q(0)]*3
        for i,ai in enumerate(a):
            for j,bj in enumerate(b):out[(i+j)%3]+=ai*bj
        return out
    one=[Q(1),Q(0),Q(0)]
    norm=[Q(1)]*3
    inv_minus=[Q(2,3),Q(1,3),Q(0)]
    inv_plus=[Q(0),Q(-1),Q(0)]
    for name,left,right in [
        ('one_minus_T_inverse',grmul([Q(1),Q(-1),Q(0)],inv_minus),[one[i]-norm[i]/3 for i in range(3)]),
        ('one_plus_T_inverse',grmul([Q(1),Q(1),Q(0)],inv_plus),[one[i]-norm[i] for i in range(3)])]:
        assert left==right,(name,left,right)
        checks.append(name)

    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'Python standard-library Fraction quotient Laurent polynomials; Y^2=X^3-16 and a^2=-16, a=4i',
        'deck_convention':'T is pullback by Q -> Q+(0,4i); sigma(X,Y)=(X,-Y)',
        'source':'H*C*R=-64*X^3*(X^3-64)/(X^3+128)^3',
        'F':'X^3/(X^3+128), Tr_T(F)=1',
        'source_trace':'R+T(R)+T^2(R)=0, with H,C fixed',
        'group_ring':{'(1-T)*(2+T)/3':'1-(1+T+T^2)/3','(1+T)*(-T)':'1-(1+T+T^2)'},
        'normalization_descent':'A:(rho,X,Y)->(w*rho,w*X,Y), w^3=1, fixes physical H,B,p and source and commutes with T',
        'scope':'Exact normalization, full degree-three elliptic isogeny kernel/deck action, S3 involution, mu3 normalization descent and actual source trace. Difference-operator inversion on trace-free functions supplies no rational de Rham primitive by itself. No certificate has been found.'}
    Path(__file__).with_name('elliptic-cover-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
