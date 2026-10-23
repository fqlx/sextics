#!/usr/bin/env python3
"""Independent bare-coordinate full compact current audit; stdlib only."""
from pathlib import Path
from fractions import Fraction as Q
import itertools
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(HERE.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks=[]
    def check(name,res):
        assert not res,(name,res)
        checks.append(name)
    b=LaurentRing(['a','C','z']);p=b.laurent
    q=p('3*C-3*a*z/2')
    H=b.add(p('a**2+z**6+1'),b.mul(b.power(q,6),p('1/a**2')),b.scale(b.mul(q,p('z')),Q(1,2)))
    h=b.diff(H,'C');Ha=b.diff(H,'a');Hz=b.diff(H,'z')
    formulas={'C':b.add(b.mul(b.power(q,5),p('18/a**2')),p('3*z/2')),
        'a':b.add(p('2*a-3*z**2/4'),b.mul(b.power(q,6),p('-2/a**3')),b.mul(b.power(q,5),p('-9*z/a**2'))),
        'z':b.add(p('6*z**5-3*a*z/4'),b.scale(q,Q(1,2)),b.mul(b.power(q,5),p('-9/a')))}
    for name,actual in [('C',h),('a',Ha),('z',Hz)]:check('actual_H_'+name,b.add(actual,b.scale(formulas[name],-1)))
    N=b.add(b.scale(H,3),b.scale(b.mul(p('C'),h),-2))
    # Actual map and Piola cofactor matrix in original physical variables.
    rr=Ring(['x','y','z']);pp=rr.poly
    C=pp('x**3*z/2+x*y/3');HH=pp('1+x**6+y**6+z**6+x*y*z/2')
    def subst_laurent(poly):
        out={}
        for ex,c in poly.items():
            # Only a has negative powers; its image is the monomial x^3.
            xx=3*ex[0];term=rr.const(c)
            term=rr.mul(term,rr.power(C,ex[1]));term=rr.mul(term,rr.power(pp('z'),ex[2]))
            out=rr.add(out,{(ee[0]+xx,ee[1],ee[2]):co for ee,co in term.items()})
        return out
    check('actual_q_equals_xy',rr.add(subst_laurent(q),pp('-x*y')))
    check('actual_H_equals_target_endpoint_H',rr.add(subst_laurent(H),rr.scale(HH,-1)))
    coords=[pp('x**3'),C,pp('z')]
    jacmat=[[rr.diff(v,x) for x in rr.names] for v in coords]
    det={}
    for perm in itertools.permutations(range(3)):
        term=rr.const((-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3)))
        for i in range(3):term=rr.mul(term,jacmat[i][perm[i]])
        det=rr.add(det,term)
    check('actual_bare_coordinate_Jacobian_xcubed',rr.add(det,pp('-x**3')))
    source=b.mul(b.power(q,3),p('1/a**2'))
    check('immutable_source_density_bare',rr.add(rr.mul(subst_laurent(source),det),pp('-y**3')))
    piola=[[pp('x/3'),{},{}],[rr.scale(rr.diff(C,'x'),-1),pp('3*x**2'),rr.scale(rr.mul(pp('3*x**2'),rr.diff(C,'z')),-1)],[{},{},pp('x**3')]]
    for i in range(3):
        for j in range(3):
            prod=rr.add(*(rr.mul(jacmat[i][k],piola[k][j]) for k in range(3)))
            check('Piola_inverse_cofactor_'+str(i)+'_'+str(j),rr.add(prod,rr.scale(det,-1) if i==j else {}))
    for j in range(3):check('Piola_divergence_column_'+str(j),rr.add(*(rr.diff(piola[i][j],rr.names[i]) for i in range(3))))
    # Euler column checked directly against the saved original connection.
    er=Ring(['H','C','h']);ep=er.poly
    L=ep('4*H*(4*C**6-729*H**4)');en=ep('3*H-2*C*h')
    data=json.loads((HERE.parent.parent/'endpoint/reconstructed-connection.json').read_text())
    for i in range(4):
        mh=er.cleared(data['H']['columns'][0][i],L);mc=er.cleared(data['C']['columns'][0][i],L)
        t1=er.add(mc,er.mul(ep('h'),mh))
        check('actual_bare_Euler_H_column0_'+str(i),er.add(er.mul(en,mh),er.mul(ep('2*C'),t1),er.scale(L,2) if i==0 else {}))
    # Generic differential polynomial calculation with all d_j coefficient
    # derivatives and all four cyclic rows. Only N is localized.
    names=['C','N0','N1','P0','P1','Ua','Wz','F0','F1']+['G'+str(j) for j in range(5)]+['d'+str(i)+str(j) for i in range(4) for j in range(4)]
    r=Ring(names);rp=r.poly
    shift={'C':r.const(1),'N0':rp('N1'),'P0':rp('P1'),'F0':rp('F1')}
    for j in range(4):shift['G'+str(j)]=rp('G'+str(j+1))
    for i in range(4):
        for j in range(3):shift['d'+str(i)+str(j)]=rp('d'+str(i)+str(j+1))
    def dp(poly):return r.add(*(r.mul(r.diff(poly,var),dv) for var,dv in shift.items()))
    class F:
        def __init__(self,n=None,k=0):self.n=n or {};self.k=k
        def __add__(self,t):
            t=cf(t);k=max(self.k,t.k)
            return F(r.add(r.mul(self.n,r.power(rp('N0'),k-self.k)),r.mul(t.n,r.power(rp('N0'),k-t.k))),k)
        def __neg__(self):return F(r.scale(self.n,-1),self.k)
        def __sub__(self,t):return self+-cf(t)
        def __mul__(self,t):
            t=cf(t);return F(r.mul(self.n,t.n),self.k+t.k)
        def deriv(self):return F(r.add(r.mul(dp(self.n),rp('N0')),r.scale(r.mul(self.n,rp('N1')),-self.k)),self.k+1)
    def cf(t):return t if isinstance(t,F) else F(r.const(t))
    def ff(t):return F(rp(t))
    def D(t,k=1):
        for _ in range(k):t=t.deriv()
        return t
    ds=[ff('d'+str(i)+'0') for i in range(4)];g=ff('G0');P=F(rp('P0'),1)
    standard=[-D(g,3)-D(ds[3]*g,2)+D(ds[2]*g)-ds[1]*g,D(g,2)+D(ds[3]*g)-ds[2]*g,-D(g)-ds[3]*g,g]
    v=list(standard);v[0]=v[0]+ff('2*C')*P
    Lstar=D(g,4)+D(ds[3]*g,3)-D(ds[2]*g,2)+D(ds[1]*g)-ds[0]*g
    horizontal=[ff('Ua+Wz')-P*2,-ff('2*C')*P,cf(0),cf(0)]
    out=[D(v[i])+ds[i]*v[3]+(v[i-1] if i else cf(0))+horizontal[i] for i in range(4)]
    want=-Lstar+ff('Ua+Wz')+ff('2*C')*D(P)
    for i in range(4):check('all_four_bare_reconstruction_rows_'+str(i),(out[i]-(want if i==0 else cf(0))).n)
    # The restoration current C*F0 has rows (F0+C*F1,C*F0,0,0).
    restoration=[D(ff('C*F0')),ff('C*F0'),cf(0),cf(0)]
    for i in range(4):
        residual=restoration[i]+(-ff('C*F1') if i==0 else cf(0))-(ff('F0') if i==0 else (ff('C*F0') if i==1 else cf(0)))
        check('actual_source_restore_row_'+str(i),residual.n)
    # Bare cyclicity is triangular: delta(s_j)=r*s_(j+1)
    # -(2+2j)h*s_j/(3H). Leading diagonal is 1,r,r^2,r^3.
    # A physical point verifies the rational determinant factor is not zero.
    point={'a':Q(1),'C':Q(1,3),'z':Q(0)}
    def ev(poly):return sum(co*point['a']**ex[0]*point['C']**ex[1]*point['z']**ex[2] for ex,co in poly.items())
    hv,nv=ev(H),ev(N);cv=point['C'];rv=nv/(3*hv)
    determinant=rv**6*(-16533720*cv**2*hv**4)/(4*cv**6-729*hv**4)**3
    assert hv==3 and nv==-3 and determinant
    checks.append('bare_cyclic_triangular_rank_nonzero_on_actual_point')
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'independent standard-library Fraction polynomial/Laurent arithmetic and arbitrary cyclic coefficient jets',
        'scope':'Complete scalar reduction and reconstruction for all rational currents in the compact rank-four module. All bare a,C,z directions retained. U=W=0 is only the previously excluded relative subproblem. No forcing solution or certificate is asserted.'}
    (HERE/'bare-full-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
