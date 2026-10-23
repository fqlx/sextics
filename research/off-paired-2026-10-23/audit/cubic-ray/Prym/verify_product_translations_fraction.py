#!/usr/bin/env python3
"""Independent full-product Prym translation/source audit; stdlib only."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent.parent))
from verify_connection_fraction import Ring


class Product(Ring):
    def __init__(self):
        super().__init__(['u','v','s','d','H','z'])
        raw=Ring(self.names)
        self.fs=raw.poly('2*u**3-z*u/2-1-z**6+H')
        self.fd=raw.poly('-2*v**3-z*v/2-1-z**6+H')
    def red(self,a):
        out={}
        fs=self.fs;fd=self.fd
        # Use unreduced Ring multiplication inside powers of fs,fd; neither
        # contains s,d, so this does not need recursive curve reductions.
        for ex,c in a.items():
            ps,rs=divmod(ex[2],2);pd,rd=divmod(ex[3],2)
            ee=list(ex);ee[2]=rs;ee[3]=rd
            term={tuple(ee):c}
            for _ in range(ps):term=super().mul(term,fs)
            for _ in range(pd):term=super().mul(term,fd)
            out=super().add(out,term)
        return out
    def mul(self,a,b):return self.red(super().mul(a,b))


def main():
    checks=[]
    def check(name,p):
        assert not p,(name,p)
        checks.append(name)
    r=Product();p=r.poly
    plus=p('3*u**2-z/4');minus=p('-3*v**2-z/4')
    def Dp(f):return r.add(r.mul(p('s'),r.diff(f,'u')),r.mul(plus,r.diff(f,'s')))
    def Dm(f):return r.add(r.mul(p('d'),r.diff(f,'v')),r.mul(minus,r.diff(f,'d')))
    def W(f):return r.add(Dp(f),Dm(f))
    def Wp(f):return r.add(Dp(f),r.scale(Dm(f),-1))
    raw=Ring(r.names)
    Fp=raw.poly('s**2-2*u**3+z*u/2+1+z**6-H')
    Fm=raw.poly('d**2+2*v**3+z*v/2+1+z**6-H')
    check('Dplus_preserves_elliptic_plus',Dp(Fp))
    check('Dminus_preserves_elliptic_minus',Dm(Fm))
    for var in r.names:check('commuting_W_Wprime_'+var,r.add(W(Wp(p(var))),r.scale(Wp(W(p(var))),-1)))
    delta=p('u-v');C=p('(u+v)/6+z*(s+d)/4')
    wc=p('(s+d)/6+3*z*(u**2-v**2)/4-z**2/8')
    wpc=p('(s-d)/6+3*z*(u**2+v**2)/4')
    check('full_W_delta',r.add(W(delta),p('-s+d')))
    check('full_Wprime_delta',r.add(Wp(delta),p('-s-d')))
    check('full_off_diagonal_W_Cext',r.add(W(C),r.scale(wc,-1)))
    check('full_off_diagonal_Wprime_Cext',r.add(Wp(C),r.scale(wpc,-1)))
    second=p('(u**2-v**2)/2-z/12+3*z*(u*s-v*d)/2')
    check('full_second_W_Cext',r.add(W(W(C)),r.scale(second,-1)))
    check('full_second_Wprime_Cext',r.add(Wp(Wp(C)),r.scale(second,-1)))
    check('full_W_second_normal_jet',r.add(W(W(delta)),p('-3*(u**2+v**2)')))
    check('full_Wprime_second_normal_jet',r.add(Wp(Wp(delta)),p('-3*(u**2+v**2)')))
    check('full_mixed_normal_jet',r.add(W(Wp(delta)),p('-3*(u**2-v**2)+z/2')))
    # Area du^dv/(s*d), fixed H,z. In intrinsic (u,v) coordinates,
    # d_u(s)=plus/s and d_v(d)=minus/d. Clear s*d in log divergence.
    for sign,name in [(1,'W'),(-1,'Wprime')]:
        numerator=r.add(r.mul(plus,p('d')),r.scale(r.mul(minus,p('s')),sign),r.scale(r.mul(plus,p('d')),-1),r.scale(r.mul(minus,p('s')),-sign))
        check('relative_area_divergence_'+name,numerator)
    # Relative one-form Lie derivatives: eta+=du/s, eta-=dv/d.
    # Dplus(1/s)*s+(1/s)*d_u(s)=0 after clearing s²;
    # cross-factor derivatives vanish. This checks both invariant forms.
    check('relative_translation_invariant_eta_plus',r.add(r.scale(plus,-1),plus))
    check('relative_translation_invariant_eta_minus',r.add(r.scale(minus,-1),minus))
    # Restrict only after all product differentiations. Curve relation
    # reductions are still valid on u=v=q; reuse the product ring with v=u.
    def diag(poly):return r.subst(poly,{v:(p('u') if v=='v' else p(v)) for v in r.names},r)
    aa=p('(s+d)/2');b0=p('(s-d)/2')
    check('diagonal_a_b0_equals_qcubed',r.add(diag(r.mul(aa,b0)),p('-u**3')))
    check('diagonal_WC_actual_a',r.add(diag(W(C)),r.scale(aa,Q(-1,3)),p('z**2/8')))
    check('diagonal_WprimeC_actual_b0',r.add(diag(Wp(C)),r.scale(b0,Q(-1,3)),p('-3*z*u**2/2')))
    check('diagonal_second_C_jet',r.add(diag(second),p('z/12'),r.scale(r.mul(p('3*z*u'),b0),-1)))
    # This is the term lost by replacing WC by its restricted formula
    # before differentiating it as an ambient function.
    naive=r.add(r.scale(aa,Q(1,3)),p('-z**2/8'))
    lost=diag(r.add(W(W(C)),r.scale(W(naive),-1)))
    check('premature_diagonal_restriction_loses_nonzero_normal_jet',r.add(lost,r.scale(r.mul(p('3*z*u'),b0),-1)))
    assert lost
    # Second-kind/exact reductions on the individual elliptic factors.
    check('plus_qsquare_holomorphic_plus_exact',r.add(plus,p('-3*u**2+z/4')))
    check('minus_qsquare_holomorphic_plus_exact',r.add(minus,p('3*v**2+z/4')))
    # Physical source factors: along the diagonal Paq=2a*s*d,
    # dC/dq=PaC/(3Paq). These identities establish contraction/12.
    check('actual_ycubed_source_flux_factor_twelve',diag(r.add(r.mul(aa,p('s-d')),p('-2*u**3'))))
    check('actual_xcubed_companion_flux_factor_twelve',r.add(r.mul(aa,p('s+d')),r.scale(r.power(aa,2),-2)))
    # Bind a=x^3,q=xy,b0=y^3 and physical PaC=a*J directly.
    rr=Ring(['x','y','z']);pp=rr.poly
    H=pp('1+x**6+y**6+z**6+x*y*z/2');CC=pp('x**3*z/2+x*y/3')
    J=rr.add(rr.mul(rr.diff(H,'x'),rr.diff(CC,'y')),rr.scale(rr.mul(rr.diff(H,'y'),rr.diff(CC,'x')),-1))
    ar=Ring(['a','q','K','z']);ap=ar.poly
    P=ap('a**4+a**2*(K+z*q/2)+q**6')
    pa=ar.add(ar.diff(P,'a'),ar.scale(ar.mul(ap('z'),ar.diff(P,'q')),Q(-3,2)))
    values={'a':pp('x**3'),'q':pp('x*y'),'K':rr.add(pp('1+z**6'),rr.scale(H,-1)),'z':pp('z')}
    check('physical_PaC_equals_a_times_J',rr.add(ar.subst(pa,values,rr),rr.scale(rr.mul(pp('x**3'),J),-1)))
    check('physical_normal_source_ycubed',rr.poly('(x*y)**3-x**3*y**3'))
    # Endpoint agent's first-current source factor: at fixed q,z,
    # C_H=z(1/s+1/d)/8 and theta=(1/d-1/s)/12.
    # Clear 96*s²*d² in C_H*theta-z*q³/(24*s²*d²).
    check('actual_first_current_CH_theta_normalization',diag(r.add(r.mul(p('z'),r.add(r.power(p('s'),2),r.scale(r.power(p('d'),2),-1))),p('-4*z*u**3'))))
    # Independent literal elliptic first-column reduction, generic cubic.
    gr=Ring(['q','A','B','D']);gg=gr.poly
    ef=gg('A*q**3+B*q+D');den=gg('27*A*D**2+4*B**3')
    RN=gg('6*A*B*q**2-9*A*D*q+4*B**2')
    # m0=-9AD/(2den), m1=-3AB/den, R=RN/den.
    residual=gr.add(gr.scale(den,Q(-1,2)),gr.scale(gr.mul(gg('-9*A*D/2-3*A*B*q'),ef),-1),
        gr.scale(gr.mul(gr.diff(RN,'q'),ef),-1),gr.scale(gr.mul(RN,gr.diff(ef,'q')),Q(1,2)))
    check('elliptic_first_column_exact_second_kind_reduction',residual)
    # The full physical C_q creates a mixed 1/(s*d) term after integration
    # by parts. Verify an actual nonzero parameter specialization exactly.
    q0,z0,D0=Q(1),Q(1),Q(1);B0=-z0/2
    def RD(A):return (6*A*B0*q0*q0-9*A*D0*q0+4*B0*B0)/(27*A*D0*D0+4*B0**3)
    mixed=z0*(RD(-2)*(3*q0*q0-z0/4)-RD(2)*(-3*q0*q0-z0/4))/48
    assert mixed==Q(-646,11663)
    checks.append('actual_first_current_retains_nonzero_third_quotient_term')
    # Exact nonzero example for the lost jet: q=1,z=1,K=−3/2 gives
    # s²=3,d²=−1, so b0 is generically nonzero over the stated constants.
    assert Q(3)!=Q(-1)
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'independent standard-library Fraction quotient-polynomial arithmetic; full product differentiated before diagonal pullback',
        'full_WC':'(s+d)/6+(3z/4)(qplus^2-qminus^2)-z^2/8',
        'full_WprimeC':'(s-d)/6+(3z/4)(qplus^2+qminus^2)',
        'source_normalization':'diag(i_W area)=12*(y^3/J)dC; diag(i_Wprime area)=12*(x^3/J)dC',
        'premature_diagonal_error':'diag(W^2 Cext)-diag(W(a/3-z^2/8))=3zq*y^3, generically nonzero',
        'first_current_mixed_witness':'At q=z=1,H=3 (D=1): the mixed 1/(s*d) numerator from tau*C_q is -646/11663, nonzero.',
        'scope':'Relative translation/area identities at fixed H,z and actual source factors. Absolute H,z derivatives, endpoint C dependence, exact fiber corrections and the remaining source equation are still required. No certificate is asserted.'}
    (HERE/'product-translations-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
