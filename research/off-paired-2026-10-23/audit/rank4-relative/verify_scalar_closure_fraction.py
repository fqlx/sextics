#!/usr/bin/env python3
"""Independent scalar adjoint/current audit; standard-library Fraction only.

Reads the endpoint connection data, not either primary verification script.
Polynomial clearing checks cyclicity, the actual finite-coordinate map and
commuting derivations. A small linear differential-expression algebra checks
unrestricted elimination and all reconstruction rows with arbitrary jets.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring


def main():
    checks=[]
    def check(name,p):
        assert not p,(name,p)
        checks.append(name)
    data_path=HERE.parent.parent/'endpoint/reconstructed-connection.json'
    data=json.loads(data_path.read_text())
    r=Ring(['H','C']); p=r.poly
    delta=p('4*C**6-729*H**4'); ell=r.scale(r.mul(p('H'),delta),4)
    mats={v:[[r.cleared(data[v]['columns'][j][i],ell) for j in range(4)] for i in range(4)] for v in ['H','C']}
    mm=lambda m,b:[r.add(*(r.mul(m[i][j],b[j]) for j in range(4))) for i in range(4)]
    # s_j=N_j/ell^j. The fixed common denominator avoids symbolic CAS algebra.
    cols=[[p('1'),{},{},{}]]
    for j in range(4):
        old=cols[-1]; prod=mm(mats['C'],old)
        cols.append([r.add(r.mul(ell,r.diff(old[i],'C')),r.scale(r.mul(old[i],r.diff(ell,'C')),-j),prod[i]) for i in range(4)])
    cden=r.mul(p('C**2'),delta)
    cnum=[p('-55*C**4'),p('-309*C**5'),p('-271*C**6+1458*H**4'),p('-2*C*(32*C**6+729*H**4)')]
    for i in range(4):
        check('cyclic_relation_row_'+str(i),r.add(r.mul(cden,cols[4][i]),*(r.scale(r.mul(r.mul(cnum[j],cols[j][i]),r.power(ell,4-j)),-1) for j in range(4))))
    for j in range(4):
        prod=mm(mats['H'],cols[j])
        for i in range(4):
            lhs=r.add(r.mul(ell,r.diff(cols[j][i],'H')),r.scale(r.mul(cols[j][i],r.diff(ell,'H')),-j),prod[i])
            check('H_column_'+str(j)+'_'+str(i),r.add(r.mul(p('3*H'),lhs),r.scale(r.mul(ell,cols[j][i]),2+2*j),r.mul(p('2*C'),cols[j+1][i])))
    det={}
    for perm in permutations(range(4)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
        term=p('1')
        for j,i in enumerate(perm):term=r.mul(term,cols[j][i])
        det=r.add(det,r.scale(term,sign))
    check('cyclic_determinant_complete_rank_four',r.add(r.mul(det,r.power(delta,3)),r.mul(p('16533720*C**2*H**4'),r.power(ell,6))))

    # Rational coefficient arithmetic localized only at C,H,Delta. This uses
    # denominator exponent vectors and polynomial lcm clearing, no CAS gcd.
    bases=[p('C'),p('H'),delta]
    class Fr:
        def __init__(self,n=None,d=(0,0,0)):
            self.n=n or {};self.d=d
        def __add__(self,b):
            b=coerce(b);ds=tuple(max(x,y) for x,y in zip(self.d,b.d))
            def lift(v):
                n=v.n
                for base,k,j in zip(bases,ds,v.d):n=r.mul(n,r.power(base,k-j))
                return n
            return Fr(r.add(lift(self),lift(b)),ds)
        def __neg__(self):return Fr(r.scale(self.n,-1),self.d)
        def __sub__(self,b):return self+-coerce(b)
        def __mul__(self,b):
            b=coerce(b);return Fr(r.mul(self.n,b.n),tuple(x+y for x,y in zip(self.d,b.d)))
        def deriv(self,var):
            out=Fr(r.diff(self.n,var),self.d)
            for j,(base,k) in enumerate(zip(bases,self.d)):
                if k:
                    d=list(self.d);d[j]+=1
                    out=out+Fr(r.scale(r.mul(self.n,r.diff(base,var)),-k),tuple(d))
            return out
    def coerce(x):return x if isinstance(x,Fr) else Fr(r.const(x))
    one=coerce(1);zero=coerce(0)
    cv=[Fr(n,(2,0,1)) for n in cnum]
    e=Fr(p('-2*C/3'),(0,1,0))
    # An Expr is linear in arbitrary coefficient jets. Keys are (name,C,H,z).
    def term(name,coeff=one):return {(name,0,0,0):coeff}
    def add(*xs):
        out={}
        for x in xs:
            for k,v in x.items():out[k]=out.get(k,zero)+v
        return {k:v for k,v in out.items() if v.n}
    def scale(x,c):return {k:v*coerce(c) for k,v in x.items() if v.n and coerce(c).n}
    def deriv(x,var):
        out={};idx={'C':1,'H':2,'z':3}[var]
        for k,v in x.items():
            if var!='z':out=add(out,{k:v.deriv(var)})
            new=list(k);new[idx]+=1
            out=add(out,{tuple(new):v})
        return out
    def powerD(x,n,var='C'):
        for _ in range(n):x=deriv(x,var)
        return x
    def check_expr(name,x):
        check(name,{k:v.n for k,v in x.items() if v.n})
    def dc(x):return deriv(x,'C')
    def nc(v):return [add(scale(v[3],cv[i]),v[i-1] if i else {}) for i in range(4)]
    def conn(v,var):
        if var=='C':m=nc(v)
        elif var=='H':m=[add(scale(nc(v)[i],e),scale(v[i],Fr(p(str(Q(-(2+2*i),3))),(0,1,0)))) for i in range(4)]
        else:m=[{} for _ in range(4)]
        return [add(deriv(v[i],var),m[i]) for i in range(4)]
    def E(v):return add(*(scale(powerD(v[i],i),(-1)**i) for i in range(4)))
    def B(v):return [add(v[1],scale(dc(v[2]),-1),powerD(v[3],2)),add(v[2],scale(dc(v[3]),-1)),v[3],{}]
    def Lstar(f):return add(powerD(f,4),powerD(scale(f,cv[3]),3),scale(powerD(scale(f,cv[2]),2),-1),dc(scale(f,cv[1])),scale(f,-cv[0]))
    def T(x):return add(deriv(x,'H'),scale(dc(x),-e))
    u=[term('u'+str(i)) for i in range(4)];v=[term('v'+str(i)) for i in range(4)];w=[term('w'+str(i)) for i in range(4)]
    bv=B(u);cb=conn(bv,'C')
    for i in range(4):check_expr('unrestricted_scalar_reduction_row_'+str(i),add(u[i],scale(E(u),-1) if i==0 else {},scale(cb[i],-1)))
    check_expr('arbitrary_C_current_adjoint',add(E(conn(v,'C')),Lstar(v[3])))
    total=[add(conn(u,'H')[i],conn(v,'C')[i],conn(w,'z')[i]) for i in range(4)]
    compressed=add(scale(Lstar(add(v[3],scale(u[3],e))),-1),T(E(u)),deriv(E(w),'z'))
    check_expr('arbitrary_full_current_compression',add(E(total),scale(compressed,-1)))
    # Direct all-four-row reconstruction from arbitrary f,U,W.
    f=term('f');U=term('U');W=term('W')
    ts=[add(scale(powerD(f,3),-1),scale(powerD(scale(f,cv[3]),2),-1),dc(scale(f,cv[2])),scale(f,-cv[1])),
        add(powerD(f,2),dc(scale(f,cv[3])),scale(f,-cv[2])),add(scale(dc(f),-1),scale(f,-cv[3])),f]
    us=[U,{},{},{}];vs=[add(ts[0],scale(U,-e)),*ts[1:]];ws=[W,{},{},{}]
    reconstructed=[add(conn(us,'H')[i],conn(vs,'C')[i],conn(ws,'z')[i]) for i in range(4)]
    wanted=add(scale(Lstar(f),-1),T(U),deriv(W,'z'))
    for i in range(4):check_expr('full_reconstruction_row_'+str(i),add(reconstructed[i],scale(wanted,-1) if i==0 else {}))
    # Independent differential-operator Euler factorization on an arbitrary g.
    g=term('g');fg=scale(g,Fr(r.mul(p('C**2'),delta)))
    def theta(x):return scale(dc(x),Fr(p('C')))
    def factors(x,ls):
        for A,B0 in ls:x=add(scale(theta(x),A),scale(x,B0))
        return x
    rhs=add(scale(factors(g,[(1,4),(1,4),(2,-1),(2,5)]),Fr(p('C**4'))),scale(factors(g,[(1,0),(1,-1),(1,2),(1,3)]),Fr(p('-729*H**4'),(2,0,0))))
    check_expr('denominator_free_Euler_adjoint_factorization',add(Lstar(fg),scale(rhs,-1)))
    # Both exact source shifts, with arbitrary physical coefficient phi.
    phi=term('phi');orig=[scale(phi,Fr(p('1/9'),(0,1,0))),scale(phi,Fr(p('C/9'),(0,1,0))),{},{}]
    hs=conn([scale(phi,Q(-1,6)),{},{},{}],'H')
    cs=conn([scale(phi,Fr(p('C/9'),(0,1,0))),{},{},{}],'C')
    for i in range(4):
        check_expr('correction_source_shift_row_'+str(i),add(hs[i],scale(deriv(phi,'H'),Q(1,6)) if i==0 else {},scale(orig[i],-1)))
        sig=scale(dc(phi),Fr(p('-C/9'),(0,1,0)))
        check_expr('original_C_source_shift_row_'+str(i),add(cs[i],sig if i==0 else {},scale(orig[i],-1)))

    # Physical finite-coordinate map and density, independently in original x,y,z.
    rr=Ring(['x','y','z']);pp=rr.poly
    H=pp('1+x**6+y**6+z**6+x*y*z/2');C=pp('x**3*z/2+x*y/3')
    J=rr.add(rr.mul(rr.diff(H,'x'),rr.diff(C,'y')),rr.scale(rr.mul(rr.diff(H,'y'),rr.diff(C,'x')),-1))
    pr=Ring(['a','H','C','z']);pol=pr.poly
    q=pol('3*C-3*a*z/2');P=pr.add(pol('a**4'),pr.power(q,6),pr.mul(pol('a**2'),pr.add(pol('z**6+1-H'),pr.scale(pr.mul(q,pol('z')),Q(1,2)))))
    Pa=pr.diff(P,'a');Paa=pr.diff(Pa,'a')
    subst={'a':pp('x**3'),'H':H,'C':C,'z':pp('z')}
    check('actual_target_P_is_zero',pr.subst(P,subst,rr))
    check('actual_target_Pa_equals_xcubed_J',rr.add(pr.subst(Pa,subst,rr),rr.scale(rr.mul(pp('x**3'),J),-1)))
    check('actual_target_q_equals_xy',rr.add(pr.subst(q,subst,rr),pp('-x*y')))
    Avec={b:pr.scale(pr.diff(P,b),-1) for b in ['H','C','z']}
    expected={'H':pol('a**2'),'C':pr.add(pr.scale(pr.power(q,5),-18),pol('-3*a**2*z/2')),
        'z':pr.add(pr.scale(pr.mul(pol('a'),pr.power(q,5)),9),pr.scale(pr.mul(pol('a**2'),pr.add(pol('6*z**5-3*a*z/4'),pr.scale(q,Q(1,2)))),-1))}
    for b in Avec:check('physical_a_'+b,pr.add(Avec[b],pr.scale(expected[b],-1)))
    for b,c in [('H','C'),('H','z'),('C','z')]:
        def D_Aquot(A,base):
            return pr.add(pr.mul(pr.add(pr.mul(pr.diff(A,base),Pa),pr.scale(pr.mul(A,pr.diff(Pa,base)),-1)),Pa),pr.mul(Avec[base],pr.add(pr.mul(pr.diff(A,'a'),Pa),pr.scale(pr.mul(A,Paa),-1))))
        check('physical_commutator_'+b+c,pr.add(D_Aquot(Avec[c],b),pr.scale(D_Aquot(Avec[b],c),-1)))
    # D_H(q^3/Pa), all q_a and Pa_H contributions retained, clear Pa^3.
    q3=pr.power(q,3)
    phiH=pr.add(pr.mul(pr.add(pr.mul(pr.diff(q3,'H'),Pa),pr.scale(pr.mul(q3,pr.diff(Pa,'H')),-1)),Pa),pr.mul(Avec['H'],pr.add(pr.mul(pr.diff(q3,'a'),Pa),pr.scale(pr.mul(q3,Paa),-1))))
    formula=pr.add(pr.mul(pr.add(pr.mul(pol('2*a'),q3),pr.scale(pr.mul(pr.mul(pol('a**2'),pr.power(q,2)),pr.diff(q,'a')),3)),Pa),pr.scale(pr.mul(pr.mul(pol('a**2'),q3),Paa),-1))
    check('actual_phi_H_full_physical_derivative',pr.add(phiH,pr.scale(formula,-1)))
    result={'status':'passed','count':len(checks),'checks':checks,'arithmetic':'independent standard-library Fraction polynomial/localized arithmetic, arbitrary commuting coefficient jets',
        'connection_sha256':hashlib.sha256(data_path.read_bytes()).hexdigest(),
        'source_binding':'P_a=x^3*(H_x C_y-H_y C_x), q=xy, hence phi=q^3/P_a=y^3/J exactly',
        'scope':'Complete equivalence for all rational currents in the compact rank-four module over the actual physical finite coefficient field. No compact row or physical base direction is restricted. Moving-pole/residue extensions lie outside this rank-four equivalence. No f,U,W solution or finite certificate is asserted.'}
    (HERE/'scalar-closure-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
