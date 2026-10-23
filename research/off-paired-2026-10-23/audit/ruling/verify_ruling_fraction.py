#!/usr/bin/env python3
"""Independent ruling differential, infinity and target source audit.

Python standard library only. No import of the candidate generator/checker.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring,record
sys.path.insert(0,str(HERE.parent/'quotient'))
from verify_piola_transfer import LaurentRing


class Quadric(LaurentRing):
    def __init__(self):
        super().__init__(['X','Y','b','A','B','Cp','rho','L'])
        self.raw=LaurentRing(self.names)
        self.xx=self.raw.laurent('(B*rho**2-B*b**2-Cp*Y**2)/A')
        self.ll=self.raw.laurent('-A/Cp')
    def red(self,poly):
        out={}
        for ex,c in poly.items():
            assert ex[0]>=0 and ex[7]>=0
            qx,rx=divmod(ex[0],2);ql,rl=divmod(ex[7],2)
            ee=list(ex);ee[0]=rx;ee[7]=rl
            term={tuple(ee):c}
            for _ in range(qx):term=self.raw.mul(term,self.xx)
            for _ in range(ql):term=self.raw.mul(term,self.ll)
            out=self.raw.add(out,term)
        return out
    def mul(self,a,b):return self.red(super().mul(a,b))


def main():
    checks=[]
    def check(name,p):
        assert not p,(name,p)
        checks.append(name)
    r=Quadric();p=r.laurent
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
    def DX(z):return z.deriv('X')-f('A*X/(B*b)')*z.deriv('b')
    def DY(z):return z.deriv('Y')-f('Cp*Y/(B*b)')*z.deriv('b')
    bx=f('-Y/(2*B*(b+rho))');by=f('X/(2*B*(b+rho))')
    check('literal_quadric_d_beta0',(DX(by)-DY(bx)-f('1/(2*B*b)')).n)
    scale=f('2*L*Cp/rho')
    # dlog[(Y-LX)/(Y+LX)] in the independent coordinates X,Y.
    dlx=f('-2*L*Y/(Y**2-L**2*X**2)')
    dly=f('2*L*X/(Y**2-L**2*X**2)')
    norm=f('-(b-rho)/(2*rho)')
    check('normalized_beta_logarithmic_X',(scale*bx-norm*dlx).n)
    check('normalized_beta_logarithmic_Y',(scale*by-norm*dly).n)
    # Residue coefficient at b=-rho is +1; at b=+rho it vanishes.
    check('finite_b_minus_rho_residue_coefficient',p('-(-rho-rho)/(2*rho)-1'))
    check('finite_b_plus_rho_log_poles_cancel',p('-(rho-rho)/(2*rho)'))
    # Centered expression agrees with the actual universal quadric.
    ce=LaurentRing(['A','B','Cp','D','E','T','a','b','q','rho']);cp=ce.laurent
    XX=cp('a+D*q/(2*A)');YY=cp('q+E/(2*Cp)')
    QQ=cp('A*a**2+B*b**2+(Cp+D**2/(4*A))*q**2+D*a*q+E*q+T')
    centered=ce.add(ce.mul(cp('A'),ce.power(XX,2)),ce.mul(cp('Cp'),ce.power(YY,2)),cp('B*b**2-B*rho**2'))
    check('actual_centered_quadric_cover',ce.add(centered,ce.scale(QQ,-1),cp('B*rho**2-E**2/(4*Cp)+T')))
    # Independent Laurent principal-part calculation at either infinity.
    sr=LaurentRing(['A','B','Cp','D','E','rho','L','b0','b1','b2','c0']);sp=sr.laurent
    Kbeta=sp('L*Cp/(B*rho)');j=sp('E/(2*Cp)')
    nums=[sp('b0**2'),sp('2*b0*b1'),sr.add(sp('b1**2+2*b0*b2'),sr.mul(sr.scale(j,3),sp('b0')))]
    inv=[sp('1/b0**2'),sp('-2*b1/b0**3'),sp('3*b1**2/b0**4-2*b2/b0**3')]
    principal=[sr.mul(Kbeta,sr.add(*(sr.mul(nums[k],inv[n-k]) for k in range(n+1)))) for n in range(3)]
    check('infinity_beta_third_order_principal',sr.add(principal[0],sr.scale(Kbeta,-1)))
    check('infinity_beta_no_second_order_principal',principal[1])
    cinfb0=sp('3*L*E/(2*B*rho*b0)')
    check('infinity_beta_residue_all_branch_jets',sr.add(principal[2],sr.scale(cinfb0,-1)))
    # raw omega=q²dq/J has leading residue -b0/(A-B*b0²).
    # Cross-multiply against -b0/(2A) and record the exact branch relation.
    check('infinity_raw_omega_residue_branch_relation',sp('-2*A*b0+b0*(A-B*b0**2)+b0*(A+B*b0**2)'))
    for sign in [1,-1]:
        # Substitute b0=sign*c0 in Laurent expressions, including negative
        # exponents; all powers of b0 occur only as monomials.
        def branch(poly):
            out={}
            for ex,co in poly.items():
                ee=list(ex);k=ee[7];ee[7]=0;ee[10]+=k
                out=sr.add(out,{tuple(ee):co*Q(sign)**k})
            return out
        cinf=sp('3*L*E/(2*B*rho*c0)')
        omegares=Q(sign)
        check('infinity_beta_hat_residue_'+str(sign),sr.add(branch(principal[2]),sr.scale(cinf,-omegares)))
        check('normalized_omega_infinity_residue_'+str(sign),sr.add(branch(sp('b0/c0')),sr.const(-sign)))
    # The correction omega is simple-pole at infinity, so the third-order
    # principal part remains in beta_hat and must not be discarded.
    assert Kbeta
    checks.append('beta_hat_retains_nonzero_infinity_second_kind_pole')
    # Actual source map from the immutable six-variable target.
    ph=LaurentRing(['x','y','z','u','v']);pp=ph.laurent
    aa,bb,qq,rr,kk,ss=[pp(t) for t in ['x**3','y**3','x*y','u**3/x**3','u*v/(x*y)','v**3/y**3']]
    coeff=[ph.add(pp('1'),ph.power(rr,2)),ph.add(pp('1'),ph.power(ss,2)),ph.scale(kk,Q(1,3)),ph.mul(pp('z/2'),kk),pp('z/2'),pp('1+z**6')]
    model=ph.add(ph.mul(coeff[0],ph.power(aa,2)),ph.mul(coeff[1],ph.power(bb,2)),ph.mul(coeff[2],ph.power(qq,2)),
        ph.mul(coeff[3],ph.mul(aa,qq)),ph.mul(coeff[4],qq),coeff[5])
    six=Ring(['X0','X1','X2','Y0','Y1','Y2'])
    fields=record(Path('/workspace/off-paired-sextics/data/off-paired/instance.rec'))[1]
    vals=dict(zip(six.names,[ph.const(1),pp('x'),pp('u'),pp('y'),pp('z'),pp('v')]))
    check('ratio_quadric_matches_immutable_F',ph.add(model,ph.scale(six.subst(six.poly(fields['F']),vals,ph),-1)))
    check('ratio_source_matches_immutable_A',ph.add(six.subst(six.poly(fields['A']),vals,ph),pp('-y**3')))
    assert Q(fields['q'])==1
    checks.append('immutable_q_equals_one')
    coords=[aa,qq,rr,kk];old=['x','y','u','v'];mat=[[ph.diff(f,v) for v in old] for f in coords]
    jac={}
    for pm in permutations(range(4)):
        term=ph.const((-1)**sum(pm[i]>pm[j] for i in range(4) for j in range(i+1,4)))
        for i in range(4):term=ph.mul(term,mat[i][pm[i]])
        jac=ph.add(jac,term)
    check('actual_ratio_Jacobian_positive_nine',ph.add(jac,pp('-9*u**3/(x*y)')))
    density=pp('x*y**4/(9*u**3)')
    check('actual_source_volume_ratio_map',ph.add(ph.mul(jac,density),pp('-y**3')))
    check('canonical_bq_source_with_outer_one_over_nine_r',ph.add(ph.mul(ph.mul(pp('9'),aa),ph.mul(rr,density)),ph.scale(ph.mul(bb,qq),-1)))
    # Universal coefficient E source and tangent derivations, directly.
    un=Ring(['A','B','C','D','E','T','a','b','q']);up=un.poly
    UQ=up('A*a**2+B*b**2+C*q**2+D*a*q+E*q+T')
    Qa,Qb,Qq=[un.diff(UQ,v) for v in ['a','b','q']]
    J=un.add(un.mul(up('a'),Qa),un.scale(un.mul(up('b'),Qb),-1))
    aE,bE=up('-a*q'),up('b*q')
    check('actual_E_tangent_cubic',un.add(un.mul(up('b'),aE),un.mul(up('a'),bE)))
    check('actual_E_tangent_quadric',un.add(un.mul(Qa,aE),un.mul(Qb,bE),un.mul(up('q'),J)))
    aq=un.add(un.scale(un.mul(up('a'),Qq),-1),un.scale(un.mul(up('q**2'),Qb),-3))
    bq=un.add(un.mul(up('b'),Qq),un.scale(un.mul(up('q**2'),Qa),3))
    check('actual_q_tangent_cubic',un.add(un.mul(up('b'),aq),un.mul(up('a'),bq),un.scale(un.mul(up('3*q**2'),J),-1)))
    check('actual_q_tangent_quadric',un.add(un.mul(Qa,aq),un.mul(Qb,bq),un.mul(Qq,J)))
    Je=un.add(un.mul(un.diff(J,'a'),aE),un.mul(un.diff(J,'b'),bE))
    minus_derivative=un.add(un.scale(un.mul(bE,J),-1),un.mul(up('b'),Je))
    source=up('-2*b*q*(3*A*a**2+D*a*q+B*b**2)')
    check('literal_minus_E_eta_b_source_numerator',un.add(minus_derivative,un.scale(source,-1)))
    # Independent double-Q normal residue, normal tangent a∂a-b∂b.
    def normal(v):return un.add(un.mul(up('a'),un.diff(v,'a')),un.scale(un.mul(up('b'),un.diff(v,'b')),-1))
    residue=un.add(un.mul(normal(up('b*q')),J),un.scale(un.mul(up('b*q'),normal(J)),-1))
    check('double_pole_bqt_source_matches_literal_variation',un.add(residue,un.scale(source,-1)))
    # The same source is -D_T(q eta_b), not just cohomologically equal.
    # For T, (a_T,b_T)=(-a,b)/J, whereas E multiplies both by q.
    aT,bT=up('-a'),up('b')
    check('actual_T_tangent_cubic',un.add(un.mul(up('b'),aT),un.mul(up('a'),bT)))
    check('actual_T_tangent_quadric',un.add(un.mul(Qa,aT),un.mul(Qb,bT),J))
    JT=un.add(un.mul(un.diff(J,'a'),aT),un.mul(un.diff(J,'b'),bT))
    minus_T_q_eta=un.add(un.scale(un.mul(up('q'),un.mul(bT,J)),-1),un.mul(up('b*q'),JT))
    check('literal_minus_T_q_eta_equals_minus_E_eta',un.add(minus_T_q_eta,un.scale(source,-1)))
    # Normalized shear S=d_D+D/(2A)d_C. Work in Cp,D coordinates:
    # A,B,Cp,E,T,lambda,rho,c0 are fixed and X=a+Dq/(2A).
    # Cartan's formula on the fixed centered quadric gives a literal
    # equality, including the exact moving-pole potential.
    sh=LaurentRing(['A','B','Cp','D','E','T','a','b','q','rho','L','c0']);sp=sh.laurent
    XX=sp('a+D*q/(2*A)');YY=sp('q+E/(2*Cp)')
    SJ=sp('2*A*a**2+D*a*q-2*B*b**2')
    Sqa=sp('2*A*a+D*q');Sqb=sp('2*B*b')
    qX=sh.mul(sp('q'),XX)
    Sa=sh.scale(sh.mul(sp('a'),qX),-1);Sb=sh.mul(sp('b'),qX)
    check('normalized_shear_preserves_Cp',sp('-D/(2*A)+D/(2*A)'))
    check('normalized_shear_tangent_cubic',sh.add(sh.mul(sp('b'),Sa),sh.mul(sp('a'),Sb)))
    check('normalized_shear_tangent_quadric',sh.add(sh.mul(Sqa,Sa),sh.mul(Sqb,Sb),sh.mul(qX,SJ)))
    # S(X)=SX/J and S(Y)=0, with SX=-B b²q/A. This is a tangent
    # vector to the centered quadric, whose coefficients are S-constant.
    SX=sh.add(Sa,sh.mul(sp('q/(2*A)'),SJ))
    SXsimple=sp('-B*b**2*q/A')
    check('normalized_shear_centered_X_velocity',sh.add(SX,sh.scale(SXsimple,-1)))
    check('normalized_shear_centered_quadric_tangency',sh.add(sh.mul(sp('A'),sh.mul(XX,SX)),sh.mul(sp('B*b'),Sb)))
    # d beta = lambda Cp/(B rho b) dX wedge dY; hence i_S d beta
    # is -lambda Cp/(A rho) q eta_b after restricting to C1.
    contraction=sh.mul(sp('L*Cp/(B*rho*b)'),SX)
    compact=sp('-L*Cp*b*q/(A*rho)')
    check('normalized_shear_compact_source_coefficient',sh.add(contraction,sh.scale(compact,-1)))
    # beta=lambda Cp/(B rho) (X dY-Y dX)/(b+rho).
    # Its contraction is F_S=lambda Cp Y b²q/[A rho J(b+rho)].
    # Compare after clearing J(b+rho); no curve relation is used.
    contraction_potential=sh.mul(sp('-L*Cp/(B*rho)'),sh.mul(YY,SX))
    explicit_potential=sh.mul(sp('L*Cp*b**2*q/(A*rho)'),YY)
    check('normalized_shear_exact_moving_pole_potential',sh.add(contraction_potential,sh.scale(explicit_potential,-1)))
    # Thus S beta = -lambda Cp/(A rho)q eta_b + d_q F_S.
    # c_inf is S-constant, but omega_inf is not; retain its S column.
    # Under the T derivative, h=A rho/(lambda Cp) is NOT constant.
    # Its product with c_inf is constant, which gives the full mixed
    # parameter formula in the accompanying audit note.
    h=sp('A*rho/(L*Cp)');cinf=sp('3*L*E/(2*B*rho*c0)')
    d=sp('3*A*E/(2*B*Cp*c0)')
    check('corrected_source_infinity_product_coefficient',sh.add(sh.mul(h,cinf),sh.scale(d,-1)))
    dh=sh.mul(sh.diff(h,'rho'),sp('-1/(2*B*rho)'))
    dc=sh.mul(sh.diff(cinf,'rho'),sp('-1/(2*B*rho)'))
    check('corrected_source_infinity_product_T_derivative',sh.add(sh.mul(dh,cinf),sh.mul(h,dc)))
    check('corrected_source_h_T_derivative',sh.add(dh,sp('A/(2*B*L*Cp*rho)')))
    # Translation V=d_E+E/(2Cp)d_T keeps the centered quadric and rho
    # fixed. At fixed q it has Va=-aY/J, Vb=bY/J, VX=Va,
    # VY=1/(2Cp). Check its Cartan identity separately from the shear.
    Va=sh.scale(sh.mul(sp('a'),YY),-1);Vb=sh.mul(sp('b'),YY)
    check('translation_rho_squared_fixed',sp('E/(2*B*Cp)-E/(2*B*Cp)'))
    check('translation_tangent_cubic',sh.add(sh.mul(sp('b'),Va),sh.mul(sp('a'),Vb)))
    check('translation_tangent_quadric',sh.add(sh.mul(Sqa,Va),sh.mul(Sqb,Vb),sh.mul(YY,SJ)))
    Qq=sh.add(sh.mul(sp('2*Cp'),YY),sh.mul(sp('D'),XX))
    aqnum=sh.add(sh.scale(sh.mul(sp('a'),Qq),-1),sp('-6*B*b*q**2'))
    delta=sp('D/(2*A)')
    # The displayed expressions are J times the differential coefficients.
    v_contraction=sh.mul(sp('L*Cp/(B*rho*b)'),sh.add(Va,sh.scale(sh.mul(sp('1/(2*Cp)'),sh.add(aqnum,sh.mul(delta,SJ))),-1)))
    v_compact=sh.mul(sp('L/rho'),sh.add(sh.mul(delta,sp('b')),sp('3*q**2')))
    check('translation_compact_eta_and_infinity_columns',sh.add(v_contraction,sh.scale(v_compact,-1)))
    # F_E=i_V beta=lambda[XJ+2Cp aY²]/[2B rho J(b+rho)].
    v_potential=sh.mul(sp('L*Cp/(B*rho)'),sh.add(sh.mul(sp('1/(2*Cp)'),sh.mul(XX,SJ)),sh.scale(sh.mul(YY,Va),-1)))
    v_explicit=sh.mul(sp('L/(2*B*rho)'),sh.add(sh.mul(XX,SJ),sh.mul(sp('2*Cp*a'),sh.power(YY,2))))
    check('translation_exact_moving_pole_potential',sh.add(v_potential,sh.scale(v_explicit,-1)))
    dc_V=sh.diff(cinf,'E')
    check('translation_infinity_normalizer_derivative',sh.add(dc_V,sp('-3*L/(2*B*rho*c0)')))
    # (V c_inf)omega_inf=(3lambda/rho)q²dq/J after c0²=-A/B.
    scalar_product=sh.mul(dc_V,sp('-2*A/c0'))
    check('translation_infinity_scalar_cancels_q_squared_column',sh.add(scalar_product,sp('-3*L/rho'),sp('3*L*(A+B*c0**2)/(B*rho*c0**2)')))
    # Plain d_E differs: rho_E=E/(4B Cp rho), canceled by the
    # E/(2Cp)d_T part of V. Record both to avoid a derivative ambiguity.
    cinf_plain_E=sh.add(sh.diff(cinf,'E'),sh.mul(sh.diff(cinf,'rho'),sp('E/(4*B*Cp*rho)')))
    cinf_V_full=sh.add(cinf_plain_E,sh.mul(sp('E/(2*Cp)'),dc))
    check('translation_infinity_derivative_includes_rho_chain_rule',sh.add(cinf_V_full,sh.scale(dc_V,-1)))
    result={'status':'passed','count':len(checks),'checks':checks,'arithmetic':'independent standard-library Fraction rational/quotient arithmetic and Laurent principal parts',
        'finite_residue_convention':'R=(Y-lambda X)/(Y+lambda X), b=-rho: +1 on numerator ruling, -1 on denominator ruling',
        'infinity_principal_part':'beta=(lambda Cp/(B rho))*u^-3 du +[3lambda E/(2B rho b0)]u^-1 du+regular; no u^-2',
        'infinity_correction':'omega_inf residues (+1,-1), beta_hat=beta-c_inf omega_inf has zero infinity residues and retained third-order second-kind poles',
        'source':'eta_b=b*dq/J; source_qt=-D_E eta_b=-D_T(q eta_b)=-2bq(3Aa^2+Daq+Bb^2)dq/J^3; physical outer factor1/(9r)',
        'normalized_shear':'S=d_D+D/(2A)d_C; S beta=-lambda Cp/(A rho)q eta_b+d_q F_S, F_S=lambda Cp (q+E/(2Cp))b^2q/[A rho J(b+rho)]',
        'normalized_shear_corrected':'S beta_hat=-lambda Cp/(A rho)q eta_b+d_q F_S-c_inf S omega_inf; the infinity column is essential',
        'translation':'V=d_E+E/(2Cp)d_T; V beta=d_q F_E+(lambda/rho)(delta eta_b+3q^2dq/J), F_E=lambda[XJ+2Cp aY^2]/[2B rho J(b+rho)]',
        'translation_corrected':'V beta_hat=d_q F_E+(lambda delta/rho)eta_b-c_inf V omega_inf, because (V c_inf)omega_inf=3lambda q^2dq/(rho J)',
        'scope':'Exact ruling differential/residue/source normalization and universal parameter identities. Cartan formula supplies the literal exact moving-pole term. Actual base lifts, their density divergences, and any full source cancellation remain separate obligations; no certificate.'}
    (HERE/'ruling-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
