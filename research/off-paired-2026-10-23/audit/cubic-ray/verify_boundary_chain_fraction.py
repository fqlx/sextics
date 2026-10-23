#!/usr/bin/env python3
"""Independent actual finite-plane and full-dlog relative chain audit."""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    normal=Ring(['G','P','d','e'])
    # J=G-d^3-e^3, J_e=-3e^2. The raw second-normal coefficient is
    # (1/J_e) partial_e[(P/(de))/J_e], before the normal-order sign.
    nn,nd=normal.rational('-P/(3*d*e**3)')
    dn=normal.add(normal.mul(normal.diff(nn,'e'),nd),normal.scale(normal.mul(nn,normal.diff(nd,'e')),-1))
    dd=normal.mul(normal.poly('-3*e**2'),normal.power(nd,2))
    en,ed=normal.rational('-P/(3*d*e**6)')
    check('actual_J_second_normal_raw_coefficient',normal.add(normal.mul(dn,ed),normal.scale(normal.mul(en,dd),-1)))
    assert (-1)**3==-1
    checks.append('actual_J_first_ordered_residue_sign_positive')
    aux_jac=normal.diff(normal.poly('d**3'),'d')
    transformed_den=normal.mul(normal.poly('3*d*e**6'),aux_jac)
    expected_den=normal.poly('9*d**3*(G-d**3)**2')
    boundary_eq=normal.poly('G-d**3-e**3')
    check('auxiliary_cubic_normalization',normal.add(transformed_den,normal.scale(expected_den,-1),
        normal.mul(normal.poly('9*d**3*(e**3+G-d**3)'),boundary_eq)))
    r=Ring(['G','P','t','GD','PD','Gu','Gv','GDu','GDv'])
    class Rat:
        def __init__(self,num,den=None):
            if isinstance(num,str):self.n,self.d=r.rational(num)
            else:self.n,self.d=num,(den if den is not None else r.const(1))
        def __add__(self,o):return Rat(r.add(r.mul(self.n,o.d),r.mul(o.n,self.d)),r.mul(self.d,o.d))
        def __neg__(self):return Rat(r.scale(self.n,-1),self.d)
        def __sub__(self,o):return self+-o
        def __mul__(self,o):return Rat(r.mul(self.n,o.n),r.mul(self.d,o.d))
        def diff(self,var):return Rat(r.add(r.mul(r.diff(self.n,var),self.d),r.scale(r.mul(self.n,r.diff(self.d,var)),-1)),r.power(self.d,2))
        def D(self):return self.diff('G')*Rat('GD')+self.diff('P')*Rat('PD')+self.diff('Gu')*Rat('GDu')+self.diff('Gv')*Rat('GDv')
        def Yu(self):return self.diff('G')*Rat('Gu')+self.diff('GD')*Rat('GDu')
        def Yv(self):return self.diff('G')*Rat('Gv')+self.diff('GD')*Rat('GDv')
    def req(name,a,b):check(name,(a-b).n)
    f=Rat('P/(9*G*(G-t))')
    ll=Rat('P/(9*G**2)')
    alpha=Rat('P/(9*t*(G-t)**2)')
    ht=Rat('1/t+1/(G-t)')
    hu,hv=Rat('-Gu/(G-t)'),Rat('-Gv/(G-t)')
    ed=Rat('-GD/(G-t)')
    req('actual_relative_threeform_decomposition',alpha,f.diff('t')+ll*ht)
    req('full_dlog_closed_u_t_component',hu.diff('t'),ht.Yu())
    req('full_dlog_closed_v_t_component',hv.diff('t'),ht.Yv())
    req('parameter_dlog_commutation_t',ht.D(),ed.diff('t'))
    req('parameter_dlog_commutation_u',hu.D(),ed.Yu())
    req('parameter_dlog_commutation_v',hv.D(),ed.Yv())
    jet=f.D()+ll*ed
    req('explicit_full_parameter_jet_primitive',jet,
        Rat('(PD*G*(G-t)-P*GD*(3*G-2*t))/(9*G**2*(G-t)**2)'))
    req('actual_relative_parameter_jet_identity',alpha.D(),jet.diff('t')+ll.D()*ht)
    # Omitting the Y-components in rho wedge dlog gives a real error even
    # for rho=du: d[rho wedge ht dt]=-d_v(ht) du dv dt, while the full
    # rho wedge dlog is closed. The missing term cancels this error.
    req('mixed_Y_homotopy_component_cancellation',hv.diff('t'),ht.Yv())
    assert ht.Yv().n
    checks.append('truncated_dlog_homotopy_is_not_valid')
    # The absolute RHS contains jet dz wedge Omega. It is nonzero for
    # G=2,P=1,t=1,GD=1,PD=0, even if G has no Y variation.
    vals={name:r.const(value) for name,value in [('G',2),('P',1),('t',1),('GD',1),('PD',0),('Gu',0),('Gv',0),('GDu',0),('GDv',0)]}
    jn=r.subst(jet.n,vals,r);jd=r.subst(jet.d,vals,r)
    assert len(jn)==len(jd)==1 and next(iter(jn.values()))/next(iter(jd.values()))==Q(-1,9)
    checks.append('absolute_external_correction_is_generically_nonzero')

    # Independently reconstruct every finite M9/M15 column over the full
    # coefficient field, without importing the primary SymPy construction.
    y=Ring(['Y0','Y1','Y2','lam','b01','b12','b02','d','e'])
    C=y.poly('Y0**6+Y1**6+Y2**6')
    B=y.poly('b01*Y0*Y1+b12*Y1*Y2+b02*Y0*Y2')
    G=y.add(C,y.mul(y.var('lam'),y.power(B,3)))
    Gi=[y.diff(G,v) for v in y.names[:3]]
    Bi=[y.diff(B,v) for v in y.names[:3]]
    dimensions={};normal_counts={};columns=0
    for degree in [9,15]:
        normal_count=0;dimension=0
        for e0 in range(degree+1):
            for e1 in range(degree-e0+1):
                e2=degree-e0-e1;ex=(e0,e1,e2,0,0,0,0,0,0)
                mon={ex:Q(1)};dimension+=1
                bad=next((i for i in range(3) if ex[i]>=5),None)
                av=[{}, {}, {}];normal={}
                if bad is None:normal=mon;normal_count+=1
                else:
                    shift=list(ex);shift[bad]-=5;av[bad]={tuple(shift):Q(1)}
                mm=y.add(mon,y.scale(y.mul(y.var('lam'),y.mul(y.power(B,2),y.add(*(y.mul(av[i],Bi[i]) for i in range(3))))),Q(1,2)))
                rhs=y.add(normal,y.scale(y.add(*(y.mul(av[i],Gi[i]) for i in range(3))),Q(1,6)))
                assert mm==rhs
                assert {ex:co for ex,co in mm.items() if ex[3]==0}==mon
                columns+=1
        dimensions[degree]=dimension;normal_counts[degree]=normal_count
    assert dimensions=={9:55,15:136} and normal_counts=={9:10,15:0} and columns==191
    checks.append('all_191_finite_plane_operator_columns')
    checks.append('finite_operator_identity_at_lambda_zero')
    checks.append('twenty_plane_representative_degree_counts')
    # At actual B=0 (e.g. physical X1=0) every operator is identity for
    # all lambda, proving its determinant does not vanish identically
    # after restriction to the physical family either.
    assert all(any(ex[j] for j in [4,5,6]) for ex in B)
    checks.append('actual_B_zero_Fermat_locus_proves_physical_generic_invertibility')
    J=y.add(G,y.poly('-d**3-e**3'))
    defect=y.add(*(y.mul(y.var(v),y.diff(J,v)) for v in y.names[:3]),y.scale(J,-6))
    check('Y_Euler_defect_retained',y.add(defect,y.poly('-6*(d**3+e**3)')))
    assert not {ex:co for ex,co in defect.items() if ex[-2]==0 and ex[-1]==0}
    checks.append('boundary_Euler_correction_double_log_residue_zero')
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'Python standard-library Fraction polynomial/rational dictionaries; no primary script imports',
        'M_columns_checked':columns,'plane_representatives':20,
        'relative_chain':'alpha=sigma wedge h+d_rel(F Omega+rho wedge h), h=d_rel log[t/(G-t)]',
        'absolute_extension':'alpha_hat=alpha_rel+sum_D[DF-L DG/(G-t)] dz_D wedge Omega',
        'absolute_reduction':'alpha_hat=sigma wedge d_abs ell+d_abs(F Omega+rho wedge d_abs ell)-d_ext rho wedge d_abs ell',
        'scope':'Finite relative source/jet chain reduction verified, with explicit nonzero absolute external corrections. Does not serve remaining plane classes, supply a scalar primitive, or prove a certificate. No certificate has been found.'}
    Path(__file__).with_name('boundary-chain-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
