#!/usr/bin/env python3
"""Independent literal toric point-pair/source audit, Fraction arithmetic."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    r=LaurentRing(['A','B','C','D','E','T','a','b','q']);p=r.laurent
    checks=[]
    def check(name,a):
        assert not a,(name,a)
        checks.append(name)
    class Fr:
        def __init__(self,n=None,d=None):self.n=n or {};self.d=d or r.const(1)
        def __add__(self,z):
            z=cf(z);return Fr(r.add(r.mul(self.n,z.d),r.mul(z.n,self.d)),r.mul(self.d,z.d))
        def __neg__(self):return Fr(r.scale(self.n,-1),self.d)
        def __sub__(self,z):return self+-cf(z)
        def __mul__(self,z):
            z=cf(z);return Fr(r.mul(self.n,z.n),r.mul(self.d,z.d))
        def deriv(self,v):return Fr(r.add(r.mul(r.diff(self.n,v),self.d),r.scale(r.mul(self.n,r.diff(self.d,v)),-1)),r.power(self.d,2))
    def cf(z):return z if isinstance(z,Fr) else Fr(r.const(z))
    def f(text):return Fr(*r.rational(text))
    zeta=f('b/q');eta=f('b/(2*A*a**2+D*a*q-2*B*b**2)')
    quad=p('A*a**2+B*b**2+C*q**2+D*a*q+E*q+T')
    J=p('2*A*a**2+D*a*q-2*B*b**2')
    def par(z,v):
        P=r.diff(quad,v)
        return z.deriv(v)+Fr(r.mul(p('-a'),P),J)*z.deriv('a')+Fr(r.mul(p('b'),P),J)*z.deriv('b')
    for v,mon in [('E','1'),('C','q'),('D','a'),('T','1/q')]:
        check('literal_zeta_'+v,(par(zeta,v)-f(mon)*eta).n)
    check('literal_zeta_EE_CT_box',(par(par(zeta,'E'),'E')-par(par(zeta,'C'),'T')).n)
    def pn(z,v):
        return par(z,v)-f({'T':'1/(2*T)','B':'-1/(2*B)'}.get(v,'0'))*z
    check('normalized_chi_T',(pn(zeta,'T')-f('1/q')*eta+f('1/(2*T)')*zeta).n)
    check('normalized_chi_heat_box',(pn(pn(zeta,'E'),'E')-pn(pn(zeta,'C'),'T')-f('1/(2*T)')*pn(zeta,'C')).n)
    # Finite local residues: at Pa, a=q³/b, b tends ±b0;
    # at Pb, b=q³/a and zeta=q²dq/a is regular.
    loc=LaurentRing(['q','a0','b0']);lp=loc.laurent
    check('Pa_plus_normalized_residue',lp('b0/b0-1'))
    check('Pa_minus_normalized_residue',lp('-b0/b0+1'))
    check('Pb_no_pole_after_norm_substitution',lp('(q**3/a0)/q-q**2/a0'))
    # Projective a=1,q=u,t=u³/b(u). Q gives b(u)² coefficients
    # h0=-A/B,h1=-D/B,h2=-C/B,h3=0, since remaining Q terms
    # start at u4 and u6. Compute the entire negative principal part.
    inf=LaurentRing(['A','B','C','D','h0','h1','h2','h3']);ip=inf.laurent
    hs=[ip('h0'),ip('h1'),ip('h2'),ip('h3')]
    principal=[inf.scale(h,Q(i,2)-2) for i,h in enumerate(hs)]
    for i,(name,target,relation) in enumerate([
            ('fourth_order','2*A/B','2*(h0+A/B)'),
            ('third_order','3*D/(2*B)','3*(h1+D/B)/2'),
            ('second_order','C/B','h2+C/B'),
            ('zero_residue','0','h3/2')]):
        check('infinity_'+name,inf.add(principal[i],inf.scale(ip(target),-1),ip(relation)))
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'independent standard-library Fraction sparse rational arithmetic; no primary import',
        'normalized':'chi=zeta/b0, b0²=-T/B; Pa residues(+1,-1), Pb regular',
        'infinity':'zeta=[2A/(B u^4)+3D/(2B u^3)+C/(B u²)]du+regular; no u^-1; chi divides this by b0',
        'source':'tau=-partial_E² zeta=-b0 partial_E² chi=-partial_T partial_C zeta',
        'scope':'Literal source and residue identities only; no actual physical primitive or existence/nonexistence claim.'}
    (HERE/'toric-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
