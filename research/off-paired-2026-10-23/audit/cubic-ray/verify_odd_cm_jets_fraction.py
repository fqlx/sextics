#!/usr/bin/env python3
"""Independent exact CM odd-jet and root-trace audit, stdlib only."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


class CM(Ring):
    def __init__(self):super().__init__(['x1','x','y1','y','zeta','s'])
    def red(self,a):
        out={}
        for ex,c in a.items():
            q1,r1=divmod(ex[2],2);q2,r2=divmod(ex[3],2)
            qz,rz=divmod(ex[4],3)
            zterms=[(0,1)] if rz==0 else ([(1,1)] if rz==1 else [(0,-1),(1,-1)])
            for j in range(q1+1):
                for k in range(q2+1):
                    for iz,cz in zterms:
                        ee=list(ex);ee[0]+=3*j;ee[1]+=3*k;ee[2]=r1;ee[3]=r2;ee[4]=iz
                        out=super().add(out,{tuple(ee):c*comb(q1,j)*comb(q2,k)*(-16)**(q1+q2-j-k)*cz})
        return out
    def mul(self,a,b):return self.red(super().mul(a,b))


def main():
    checks=[]
    def check(name,p):
        assert not p,(name,p)
        checks.append(name)
    r=CM();p=r.poly
    L=p('(x1-x)*(x1-zeta*x)')
    def d1(f):return r.add(r.mul(p('2*y1'),r.diff(f,'x1')),r.mul(p('3*x1**2'),r.diff(f,'y1')))
    def d3(f):return r.add(r.mul(p('2*y'),r.diff(f,'x')),r.mul(p('3*x**2'),r.diff(f,'y')))
    def qdiff(n,d,op):return r.add(r.mul(op(n),d),r.scale(r.mul(n,op(d)),-1))
    amin=p('-zeta**2*y*(x1+zeta**2*x)');bmin=p('-x*y1')
    apl=p('-zeta**2*y1*(x1+zeta**2*x)');bpl=p('-x*y')
    for name,A,B,target in [('odd',amin,bmin,p('x')),('even',apl,bpl,{})]:
        check('CM_'+name+'_kernel_derivative',r.add(qdiff(B,L,d1),r.scale(qdiff(A,L,d3),-1),r.scale(r.mul(target,r.power(L,2)),-1)))
    A=[p('-zeta**2*(x**3-16)*(x1+zeta**2*x)'),p('-zeta**2*(x1**3-16)*(x1+zeta**2*x)')]
    bn=p('-x*y1/2')
    cn=[p('x*(x1+2*zeta**2*x)**2/2'),p('-3*x1**2*x/2')]
    for j in range(2):
        check('rational_odd_jet_'+str(j),r.add(qdiff(bn,L,d1),r.scale(qdiff(A[j],L,lambda f:r.diff(f,'x')),-1),r.scale(r.mul(cn[j],L),-1)))
    check('paired_graph_poles_cancel',r.add(A[0],r.scale(A[1],-1),r.scale(r.mul(p('zeta**2*x1**2-x**2'),L),-1)))
    check('paired_source_two_x',r.add(cn[0],r.scale(cn[1],-1),r.scale(r.mul(p('2*x'),L),-1)))
    # Explicit pullback by all three roots; the differential dx has its
    # own zeta factor. Check the normalized trace, not an unnormalized sum.
    def root(poly,j):
        return r.subst(poly,{n:(r.mul(r.var('x'),r.power(r.var('zeta'),j)) if n=='x' else r.var(n)) for n in r.names},r)
    ls=[root(L,j) for j in range(3)];common=r.mul(ls[0],r.mul(ls[1],ls[2]))
    Qms=p('x1**3-x**3')
    for i in range(2):
        n={}
        for j in range(3):
            other=r.mul(ls[(j+1)%3],ls[(j+2)%3])
            n=r.add(n,r.scale(r.mul(root(r.mul(p('x'),A[i]),j),other),Q(1,3)))
        znum=p('x**3*(x**3-16)' if i==0 else 'x**3*(x1**3-16)')
        check('normalized_root_trace_A'+str(i),r.add(r.mul(n,Qms),r.scale(r.mul(znum,common),-1)))
    n={}
    for j in range(3):
        other=r.mul(ls[(j+1)%3],ls[(j+2)%3])
        term=r.mul(root(r.mul(p('x'),bn),j),r.power(p('zeta'),j))
        n=r.add(n,r.scale(r.mul(term,other),Q(1,3)))
    check('normalized_root_trace_dx_and_ds_factor',r.add(r.mul(n,Qms),r.mul(p('x**2*x1*y1/2'),common)))
    ds=p('x1**3-s');zb=p('-x1*y1/6')
    for i in range(2):
        za=p('s*(s-16)' if i==0 else 's*(x1**3-16)')
        dn=p('(x1**3-6*s+32)/6' if i==0 else '-(5*x1**3-32)/6')
        check('traced_jet_derivative_'+str(i),r.add(qdiff(zb,ds,d1),r.scale(qdiff(za,ds,lambda f:r.diff(f,'s')),-1),r.scale(r.mul(dn,ds),-1)))
    # Cubic inverse and its full normalized trace, independent of the
    # primary SymPy polynomial inversion.
    c=LaurentRing(['p','H','B','C']);cp=c.laurent
    f=cp('C*p**3+B*p+H');g=cp('B+3*C*p**2');D=cp('4*B**3+27*C*H**2')
    def rem(a):
        out={}
        for ex,co in a.items():
            if ex[0]<3:out=c.add(out,{ex:co});continue
            ee=list(ex);ee[0]-=3
            t={tuple(ee):co}
            out=c.add(out,rem(c.mul(t,cp('-B*p/C-H/C'))))
        return out
    invn=cp('4*B**2-9*C*H*p+6*B*C*p**2')
    check('exact_cubic_inverse_g',rem(c.add(c.mul(invn,g),c.scale(D,-1))))
    num=c.mul(cp('p'),c.power(invn,2))
    moments=[cp('1'),{},cp('-2*B/(3*C)'),cp('-H/C'),cp('2*B**2/(3*C**2)'),cp('5*B*H/(3*C**2)')]
    trace={}
    for ex,co in num.items():
        ee=list(ex);power=ee[0];ee[0]=0
        trace=c.add(trace,c.mul({tuple(ee):co},moments[power]))
    check('normalized_cubic_trace_p_over_g2',c.add(trace,c.mul(cp('3*H'),D)))
    sn=cp('-64*H');sd=cp('C*p**3')
    physical_pair=c.add(c.scale(c.mul(c.mul(c.mul(cp('p**2'),sn),c.add(sn,c.scale(sd,-64))),c.power(g,2)),-1),
        c.scale(c.mul(cp('B*H*p'),c.power(c.add(sn,c.scale(sd,128)),2)),-1))
    check('root_traced_pair_actual_physical_cubic_current',rem(physical_pair))
    # The new canonical expression also proves the same tracefree
    # projection using Tr(V)=Tr(W)=0, already audited independently.
    qidentity=c.add(c.mul(c.mul(cp('2*p**2'),g),D),c.scale(c.mul(cp('H*p'),c.power(g,3)),-3),c.scale(c.mul(cp('27*H**2'),c.power(g,2)),-1),c.mul(cp('4*B*p**2'),D))
    check('paired_tracefree_canonical_V_W_identity',rem(qidentity))
    # Actual nonzero physical normal derivative: c=1,h=0,T=0,w=1,
    # e=-2,Y=3,V^2=-2; H=10/9,B=0,b1=V/3, k^3=H,x=4.
    # Here x_h=4V/(9k^2), J=HV/3, and differentiating the zero (s-64)
    # in m gives the following exact rational coefficient after cancellation.
    hv=Q(10,9);xv=Q(4);sv=xv**3
    mh=-Q(96)*xv*sv/(hv*(sv+128)**3)
    assert mh==Q(-1,320)
    checks.append('actual_source_field_nonzero_mh_equals_minus_1_over_320ascale')
    # Independently evaluate both full canonical residual rows in Q(i) at
    # the actual physical point supplied by the endpoint agent.
    class G:
        def __init__(self,a=0,b=0):self.a=Q(a);self.b=Q(b)
        def __add__(self,t):
            t=cg(t);return G(self.a+t.a,self.b+t.b)
        def __neg__(self):return G(-self.a,-self.b)
        def __sub__(self,t):return self+-cg(t)
        def __mul__(self,t):
            t=cg(t);return G(self.a*t.a-self.b*t.b,self.a*t.b+self.b*t.a)
        def __truediv__(self,t):
            t=cg(t);return self*G(t.a/(t.a*t.a+t.b*t.b),-t.b/(t.a*t.a+t.b*t.b))
        def __bool__(self):return bool(self.a or self.b)
        def __str__(self):return str(self.a)+' + ('+str(self.b)+')i'
    def cg(t):return t if isinstance(t,G) else G(t)
    bb=G(Q(5,6),Q(-1,2));b1=G(Q(1,3),Q(-1,2))
    jj=b1-bb*4;jh=(b1-bb*10)*2;dd=bb*bb*bb*4+27;ddh=bb*bb*b1*12+324
    aa=bb*Q(-27,4)/jj/dd;dv=-bb/jj;lam=jj*3/bb;kap=bb*bb*bb;tt=kap*4+27
    dah=aa*(b1/bb+12-jh/jj-ddh/dd);ddv=dv*(b1/bb-jh/jj)
    rv=dah+lam*dv*3/tt
    rw=ddv-lam*aa*2+(cg(27)-kap*2)*lam*dv/tt-1
    assert rv and rw
    checks.append('actual_Qi_point_both_full_canonical_residuals_nonzero')
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'independent standard-library Fraction quotient polynomial arithmetic and exact cubic Newton traces',
        'nonzero_remainder_witness':'At c=1,h=0,T=0,w=1,e=-2,Y=3,V^2=-2,H=10/9,B=0,x=4,k^3=10/9: a_scale*m_h=-1/320. T=0 is a regular point of the common field chart though x1 has a pole there; the witness proves m_h is not the zero field function.',
        'actual_Qi_point_residuals':{'V':str(rv),'W':str(rw)},
        'scope':'CM kernel, rational even jets, normalized root traces and cubic trace are exact. Exterior-form physical orientation is independently derived in ODD-CM-JETS-AUDIT.md. A nonzero density derivative remains; no source-carrying complete primitive is asserted.'}
    Path(__file__).with_name('odd-cm-jets-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
