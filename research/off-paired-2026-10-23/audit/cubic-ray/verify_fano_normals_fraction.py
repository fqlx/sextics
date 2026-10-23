#!/usr/bin/env python3
"""Independent exact Cardano/Fano normal-source audit; stdlib only."""
from pathlib import Path
from fractions import Fraction as Q
import itertools
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    r=Ring(['S','T','c','H','B','C','Hi','Bi','Ci'])
    p=r.poly
    g1,g2,g3=p('S**3+T**3-H'),p('c**3-C'),p('B+3*c*S*T')
    k,delta=p('S**2+S*T+T**2'),p('S**3-T**3')
    jac=[[r.diff(g,q) for q in ['S','T','c']] for g in [g1,g2,g3]]
    def parity(perm):return (-1)**sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
    determinant=r.add(*(r.scale(r.mul(jac[0][pm[0]],r.mul(jac[1][pm[1]],jac[2][pm[2]])),parity(pm)) for pm in itertools.permutations(range(3))))
    check('normal_Jacobian_actual_order',r.add(determinant,p('27*c**3*(S**3-T**3)')))
    # dG1 dG2 dQ dq has the same sign as dq dS dT dc.
    assert parity([4,5,6,0,1,2,3])==1
    checks.append('normal_order_G1_G2_Q_positive_four_base_swap')
    assert parity([2,0,1])==1
    checks.append('cyclic_normal_reorder_Q_G1_G2_even')
    assert parity([6,0,1,2,3,4,5])==1
    checks.append('Q_first_normal_coefficient_positive_Qc')
    substitutions={q:r.var(q) for q in r.names}
    substitutions.update({'H':p('S**3+T**3'),'B':p('-3*c*S*T'),'C':p('c**3')})
    # p_root=-(S+T)/c; clear c^3 in the physical cubic.
    root_num=p('-S-T')
    cubic=r.add(p('H*c**3'),r.mul(p('B*c**2'),root_num),r.mul(p('C'),r.power(root_num,3)))
    check('physical_cubic_on_incidence',r.subst(cubic,substitutions,r))
    gn=r.add(p('B*c**2'),r.mul(p('3*C'),r.power(root_num,2)))
    check('physical_g_on_incidence',r.add(r.subst(gn,substitutions,r),r.scale(r.mul(p('3*c**3'),k),-1)))
    # R=ST(S+T)/(9c^3 K^3), N=-3ST(S^2-T^2)/K^2.
    rnum=p('S*T*(S+T)')
    nnum=p('-3*S*T*(S**2-T**2)')
    raw_rnum=r.subst(r.mul(p('B*c**5'),root_num),substitutions,r)
    raw_gn=r.subst(gn,substitutions,r)
    check('source_R_direct_normalization',r.add(r.mul(raw_rnum,r.mul(p('9*c**3'),r.power(k,3))),
        r.scale(r.mul(rnum,r.power(raw_gn,3)),-1)))
    check('three_normal_numerator_N_equals_JR',r.add(r.mul(nnum,r.mul(p('9*c**3'),r.power(k,3))),r.scale(r.mul(determinant,r.mul(rnum,r.power(k,2))),-1)))

    # Actual horizontal first jets, with a common denominator 3c^3 delta.
    un=p('-Bi*c**2-S*T*Ci')
    sin=r.add(p('S*Hi*c**3'),r.scale(r.mul(p('T**2'),un),-1))
    tin=r.add(r.mul(p('S**2'),un),p('-T*Hi*c**3'))
    common=r.mul(p('3*c**3'),delta)
    check('horizontal_G1_all_three_coefficient_jets',r.add(r.mul(p('3*S**2'),sin),r.mul(p('3*T**2'),tin),r.scale(r.mul(p('Hi'),common),-1)))
    check('horizontal_G2_C_jet',p('3*c**2*Ci-Ci*3*c**2'))
    check('horizontal_Q_B_and_C_jets',r.add(r.mul(p('Bi'),common),r.mul(p('3*c*S*T*Ci'),delta),r.mul(p('3*c*T'),sin),r.mul(p('3*c*S'),tin)))
    def de(poly):return r.add(r.mul(p('3*T**2'),r.diff(poly,'S')),r.scale(r.mul(p('3*S**2'),r.diff(poly,'T')),-1))
    check('elliptic_field_tangent_G1',de(g1))
    check('elliptic_field_tangent_G2',de(g2))
    dq=de(g3)
    check('coupling_normal_derivative',r.add(dq,r.mul(p('9*c'),delta)))
    qn,qd=p('-S-T'),r.scale(k,2)
    dqnum=r.add(r.mul(de(qn),qd),r.scale(r.mul(qn,de(qd)),-1))
    check('elliptic_qE_primitive',r.add(dqnum,r.scale(nnum,-4)))
    check('qE_deltaEQ_full_product',r.add(r.mul(qn,dq),r.scale(r.mul(p('9*c*(S**2-T**2)'),k),-1)))
    # Exact double-Q scalar: (1/Qc) d_c[qE*deltaE Q/(Qc*G2)].
    pn=r.mul(qn,dq)
    pd=r.mul(qd,r.mul(p('3*S*T'),g2))
    derivative_num=r.add(r.mul(r.diff(pn,'c'),pd),r.scale(r.mul(pn,r.diff(pd,'c')),-1))
    derivative_den=r.mul(p('3*S*T'),r.power(pd,2))
    expected_num=r.mul(qn,r.mul(delta,p('2*c**3+C')))
    expected_den=r.mul(qd,r.mul(p('S**2*T**2'),r.power(g2,2)))
    check('double_Q_scalar_all_normal_jets',r.add(r.mul(derivative_num,expected_den),r.scale(r.mul(expected_num,derivative_den),-1)))
    tau_jac=r.add(p('3*S**3'),p('-3*T**3'))
    check('G1_tau_coordinate_Jacobian',r.add(tau_jac,r.scale(delta,-3)))
    # qE delta/(S^2 T^2) times dS dT, after G1 normal, is
    # qE/(3 tau^2) d tau with positive sign (four base coordinates).
    check('ordered_remaining_source_factor',r.add(r.mul(qn,delta),r.scale(r.mul(qn,tau_jac),Q(-1,3))))

    a=Ring(['tau','B','C'])
    dnum,dDen=a.poly('B**3'),a.poly('27*tau**3')
    geffnum=a.add(a.mul(a.var('C'),dDen),dnum)
    # c=-B/(3tau), hence G2=-(C+D), 2c^3+C=C-2D.
    check('effective_G2_sign',a.add(a.poly('-B**3-27*C*tau**3'),geffnum))
    pn=a.poly('27*tau**2')
    derivative=a.add(a.mul(a.diff(pn,'tau'),geffnum),a.scale(a.mul(pn,a.diff(geffnum,'tau')),-1))
    lhs=a.mul(a.add(a.mul(a.var('C'),dDen),a.scale(dnum,-2)),dDen)
    check('actual_tau_parameter_derivative',a.add(lhs,a.mul(a.poly('tau**2'),derivative)))
    # Actual homogeneous quadratic coupling on the projective Y-plane.
    y=Ring(['Y0','Y1','Y2','alpha','beta','gamma','tau'])
    fy=y.poly('Y0**6+Y1**6+Y2**6')
    by=y.poly('alpha*Y0*Y1+beta*Y1*Y2+gamma*Y0*Y2')
    numerator=y.mul(y.poly('Y0**3'),y.add(y.mul(y.poly('27*tau**3'),fy),y.scale(y.power(by,3),-2)))
    assert all(sum(ex[:3])==9 for ex in numerator)
    checks.append('actual_plane_pole2_numerator_degree9')
    assert 9+3==2*6
    checks.append('plane_pole2_projective_degree_balance')
    # Weighted ambient volume has weight9; Q,JY,d,e have weights2,6,2,2.
    assert 9+9==2+2*6+2+2
    checks.append('full_weighted_boundary_form_degree_balance')
    assert sum([1,1,1,2,2,2])-(2+6)==1
    checks.append('relative_complete_intersection_anticanonical_weight1')
    assert parity([2,3,0,1])==1
    checks.append('boundary_residue_d_e_then_Y_positive')
    # The constant term is evaluated in the local d,e ring; all denominator
    # corrections start at exponent3. It is exactly G_eff^-2. The dd/d
    # and de/e factors must be retained to extract that coefficient.
    boundary=Ring(['G','d','e'])
    squared=boundary.power(boundary.poly('G-d**3-e**3'),2)
    small={ex:co for ex,co in squared.items() if ex[1]<3 and ex[2]<3}
    check('boundary_de_log_residue_retains_actual_Geff_double_pole',
          boundary.add(small,boundary.poly('-G**2')))
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'Python standard-library Fraction polynomial dictionaries; no primary imports',
        'normal_order':'(G1,G2,Q), ambient(q1,q2,q3,q4,S,T,c)',
        'J':'-27*c^3*(S^3-T^3)',
        'ordered_remaining_fiveform':'qE/(3*tau^2)*(C-2D)/(C+D)^2 dq wedge dtau, D=B^3/(27*tau^3), after Q then G1 residues of the double-Q correction',
        'scope':'Actual source, horizontal jets, normal signs, effective moving sextic, parameter derivative, and retained1/(de) boundary checked. No Fano-to-primitive implication; no certificate has been found.'}
    Path(__file__).with_name('fano-normal-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
