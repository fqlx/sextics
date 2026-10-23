#!/usr/bin/env python3
"""Independent exact Jacobian-aware scalar-adjoint transport audit.

No SymPy and no import of a primary transport script. Universal H, H_a, H_C
and second derivative jets certify the physical vector-field identities.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring


def main():
    checks=[]
    r=Ring(['C','tau','H','A','h','AA','Ah','hh']);p=r.poly
    bases=[p('H'),p('A'),p('3*H-2*C*h'),p('tau')]
    class F:
        def __init__(self,n=None,d=(0,0,0,0)):self.n=n or {};self.d=d
        def __add__(self,b):
            b=cf(b);ds=tuple(max(i,j) for i,j in zip(self.d,b.d))
            def lift(v):
                z=v.n
                for base,i,j in zip(bases,ds,v.d):z=r.mul(z,r.power(base,i-j))
                return z
            return F(r.add(lift(self),lift(b)),ds)
        def __neg__(self):return F(r.scale(self.n,-1),self.d)
        def __sub__(self,b):return self+-cf(b)
        def __mul__(self,b):
            b=cf(b);return F(r.mul(self.n,b.n),tuple(i+j for i,j in zip(self.d,b.d)))
        def partial(self,var):
            ans=F(r.diff(self.n,var),self.d)
            for j,(base,k) in enumerate(zip(bases,self.d)):
                if k:
                    ds=list(self.d);ds[j]+=1
                    ans=ans+F(r.scale(r.mul(self.n,r.diff(base,var)),-k),tuple(ds))
            return ans
    def cf(x):return x if isinstance(x,F) else F(r.const(x))
    def v(s):return F(p(s))
    def check(name,z):
        # All root-cover equalities are identities modulo tau^3-H.
        reduced={}
        for exp,coeff in z.n.items():
            ex=list(exp);q0,ex[1]=divmod(ex[1],3);ex[2]+=q0
            key=tuple(ex);reduced[key]=reduced.get(key,Q(0))+coeff
            if not reduced[key]:del reduced[key]
        assert not reduced,(name,reduced)
        checks.append(name)
    zero=cf(0);one=cf(1)
    # A=H_a. Root-cover bare partials differentiate tau^3=H as well.
    da={'H':v('A'),'A':v('AA'),'h':v('Ah'),'tau':F(p('tau*A/3'),(1,0,0,0))}
    dc={'H':v('h'),'A':v('Ah'),'h':v('hh'),'C':one,'tau':F(p('tau*h/3'),(1,0,0,0))}
    def act(f,m):
        out=zero
        for x,coeff in m.items():out=out+f.partial(x)*coeff
        return out
    def Da(f):return act(f,da)
    def delta(f):return act(f,dc)
    rr=F(p('3*H-2*C*h/1'),(1,0,0,0))*Q(1,3)
    k=F(p('2*C/3'),(1,0,0,0))
    beta=F(p('3*H*tau**2'),(0,0,1,0))
    rho=F(p('A'),(0,0,0,2))
    tv=[F(p('3*H-2*C*h'),(1,1,0,0))*Q(1,3),k]
    bv=[F(p('-tau**2*h'),(0,1,0,0)),v('tau**2')]
    def T(f):return Da(f)*tv[0]+delta(f)*tv[1]
    def B(f):return Da(f)*bv[0]+delta(f)*bv[1]
    check('actual_root_cover_T_H',T(v('H'))-one)
    check('actual_root_cover_B_H',B(v('H')))
    check('actual_root_cover_T_tau',T(v('tau'))-F(p('tau/3'),(1,0,0,0)))
    check('actual_root_cover_B_tau',B(v('tau')))
    b=F(p('C'),(0,0,0,2))
    check('normalized_T_b_zero',T(b))
    # B(b)=tau^2/tau^2=1, including every physical a derivative.
    check('normalized_B_b_one',B(b)-one)
    check('tau_cubic_T_tangency',T(v('tau**3-H')))
    check('tau_cubic_B_tangency',B(v('tau**3-H')))
    for i in range(2):check('full_physical_commutator_component_'+str(i),B(tv[i])-T(bv[i]))
    check('physical_commutator_tau',B(T(v('tau')))-T(B(v('tau'))))
    for i in range(2):
        wanted=beta*((one if i==1 else zero)-v('h')*tv[i])
        check('physical_transverse_decomposition_'+str(i),bv[i]-wanted)
    divT=Da(rho*tv[0])+delta(rho*tv[1])
    divB=Da(rho*bv[0])+delta(rho*bv[1])
    check('full_rho_weighted_T_divergence',divT)
    check('full_rho_weighted_B_divergence',divB)
    # This coefficient is the entire zero-order defect of
    # BF=Dcal(F)-T(beta*h*F); vector-symbol coefficients were checked above.
    check('all_arbitrary_F_transport_zero_order',rho*T(beta*v('h'))-delta(rho*beta))
    # The actual covering density is Ha/tau^2; tau^3=H supplies no extra
    # factor here, since the volume is written da dC dz, not dtau db dz.
    check('finite_cover_density_exact',rho*v('tau**2')-v('A'))
    # Scalar-potential factor tau^8/(rho beta^4)=tau^2 r^4/Ha.
    lhs=F(p('tau**8'))
    for _ in range(4):lhs=lhs*F(p('3*H-2*C*h'),(1,0,0,2))*Q(1,3)
    lhs=lhs*F(p('tau**2'),(0,1,0,0))
    rhs=F(p('(3*H-2*C*h)**4*tau**2/81'),(4,1,0,0))
    check('scalar_potential_fourth_power_Jacobian_factor',lhs-rhs)
    # Coefficient scaling that proves L*(tau^8 F)=L_b*F, including order.
    src=Ring(['H','C']);sp=src.poly
    target=Ring(['tau','b']);tp=target.poly
    Delta=sp('4*C**6-729*H**4');den=src.mul(sp('C**2'),Delta)
    nums=[sp('-55*C**4'),sp('-309*C**5'),sp('-271*C**6+1458*H**4'),sp('-2*C*(32*C**6+729*H**4)')]
    vals={'H':tp('tau**3'),'C':tp('tau**2*b')}
    dd=src.subst(den,vals,target)
    db=tp('b**2*(4*b**6-729)')
    nb=[tp('-55*b**4'),tp('-309*b**5'),tp('-271*b**6+1458'),tp('-2*b*(32*b**6+729)')]
    for j in range(4):
        nn=src.subst(nums[j],vals,target)
        # c_j(H,C)*tau^(8-2j)=c_j(1,b).
        res=target.add(target.mul(target.mul(nn,tp('tau**'+str(8-2*j))),db),target.scale(target.mul(nb[j],dd),-1))
        assert not res,('normalized_companion_scaling_'+str(j),res)
        checks.append('normalized_companion_scaling_'+str(j))
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'independent standard-library Fraction polynomial/localized arithmetic with arbitrary H first and second jets',
        'scope':'Physical vector fields, finite-root density, all first-order transport terms and normalized coefficients checked identically. The fourth recurrence follows by exact induction from this identity and [B,T]=0. The monic-potential adjunction and U correction are reviewed algebraically in ADJOINT-TRANSPORT-AUDIT.md. No forcing solution is asserted.'}
    primary=HERE.parent.parent/'coupled-fresh/rank4-relative/ADJOINT-TRANSPORT.md'
    result['audited_note_sha256']=hashlib.sha256(primary.read_bytes()).hexdigest()
    (HERE/'adjoint-transport-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
