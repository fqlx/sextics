#!/usr/bin/env python3
"""Independent exact algebra for the pure-component kappa obstruction.

The proper-residue/localization proof and its limited scope are reviewed in
PURE-COMPONENT-AUDIT.md. No SymPy or construction script is imported.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring


def main():
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    # Independently verify the complete canonical kappa gauge against the
    # finite connection already audited in verify_finite_fraction.py.
    r=Ring(['H','B','C'])
    p=r.poly
    delta=p('4*B**3+27*C*H**2')
    hbc=p('H*B*C')
    hb=p('H*B')
    endpoint=Path(__file__).parents[2]/'endpoint/cubic-ray'
    finite_path=endpoint/'finite-connection-results.json'
    finite=json.loads(finite_path.read_text())
    cm=r.mul(r.var('C'),delta)
    mats={v:[[r.cleared(text,cm) for text in row] for row in finite['matrices'][v]] for v in r.names}
    sn=[r.cleared(text,r.power(delta,2)) for text in finite['source']]
    # Gauge columns are V=F-1/3 and W=HC*R in (p,p^2+2B/3C).
    gn=[[r.mul(p('-6*B*C*H'),delta),r.mul(p('H*C'),sn[0])],
        [r.mul(p('4*B**2*C'),delta),r.mul(p('H*C'),sn[1])]]
    kn=[[{},p('3*C*H**2')],[r.scale(delta,-2),p('27*C*H**2-2*B**3')]]
    dln={'H':p('-2*B*C'),'B':p('3*H*C'),'C':p('-H*B')}
    for v in r.names:
        for i in range(2):
            for j in range(2):
                residual=r.mul(hbc,r.add(r.mul(r.diff(gn[i][j],v),delta),
                                          r.scale(r.mul(gn[i][j],r.diff(delta,v)),-2)))
                residual=r.add(residual,*(r.mul(hb,r.mul(mats[v][i][k],gn[k][j])) for k in range(2)),
                    *(r.scale(r.mul(dln[v],r.mul(gn[i][k],kn[k][j])),-1) for k in range(2)))
                check('canonical_kappa_gauge_'+v+str(i)+str(j),residual)
    check('gauge_determinant_nonzero',r.add(r.mul(gn[0][0],gn[1][1]),r.scale(r.mul(gn[0][1],gn[1][0]),-1),
                         r.scale(r.mul(p('2*B**3*C**2*H'),r.power(delta,2)),-1)))

    # Universal integrating-factor first-jet coefficients: directly
    # differentiate kappa=B^3/(CH^2), retaining each coefficient derivative.
    k_num,k_den=p('B**3'),p('C*H**2')
    for v in r.names:
        direct=r.mul(hbc,r.add(r.mul(r.diff(k_num,v),k_den),
                               r.scale(r.mul(k_num,r.diff(k_den,v)),-1)))
        expected=r.mul(dln[v],r.mul(k_num,k_den))
        check('integrating_factor_first_jet_'+v,r.add(direct,r.scale(expected,-1)))
    # κ/(HC)=B³/(H³C²), clearing both parsed denominator expressions.
    check('actual_moment_normalization',r.add(r.mul(k_num,p('H**3*C**2')),
          r.scale(r.mul(p('B**3'),r.mul(k_den,p('H*C'))),-1)))

    # Necessary nonvanishing conditions for the complete coupled system.
    # Al=A(log kappa), Dl=D(log kappa), g=1/(HC).
    coupled=Ring(['k','Al','Dl','g'])
    cp=coupled.poly
    den=cp('4*k+27')
    check('coupled_divA_zero_moment',cp('k*(g+2*Al)-2*k*Al-k*g'))
    # Clear den in div[kD+2k^2A]-kg-2k(1+2k)Al, using
    # divA=-3Dl/den and divD=g+2Al-(27-2k)Dl/den.
    general=coupled.add(coupled.mul(cp('k*(g+2*Al)'),den),
        cp('-k*(27-2*k)*Dl'),coupled.mul(cp('k*Dl'),den),cp('-6*k**2*Dl'),
        coupled.mul(cp('4*k**2*Al'),den),
        coupled.scale(coupled.mul(cp('k*g+2*k*(1+2*k)*Al'),den),-1))
    check('coupled_A_logk_zero_moment',general)

    # Actual homogeneous numerator, preserving both projective gradings.
    s=Ring(['t','x','a','w','u','v'])
    h=s.poly('t**6+x**6+a**6')
    c=s.poly('w**6+u**6+v**6')
    b=s.poly('t**3*x*u*w/2+x**3*a*u*v/2+t**2*x*a*v*w/3')
    assert all((sum(ex[:3]),sum(ex[3:]))==(4,2) for ex in b)
    checks.append('B_bidegree_4_2')
    numerator=s.mul(s.poly('t**3*w**3'),s.power(b,3))
    assert all((sum(ex[:3]),sum(ex[3:]))==(15,9) for ex in numerator)
    checks.append('global_Psi_bidegree_with_projective_volumes')
    selected={ex:co for ex,co in numerator.items() if ex[4]%6==3 and ex[5]%6==3}
    check('unique_actual_Y_character_source',s.add(selected,s.poly('-t**3*x**9*a**3*w**3*u**3*v**3/8')))
    lift=s.poly('t**3*x**4*a**3*w**3*u**3*v**3/48')
    check('H_pole3_full_Jacobian_lift',s.add(s.mul(lift,s.diff(h,'x')),s.scale(selected,-1)))
    reduced=s.scale(s.diff(lift,'x'),Q(1,2))
    check('H_pole2_reduced_product',s.add(reduced,s.poly('-t**3*x**3*a**3*w**3*u**3*v**3/24')))
    assert all((sum(ex[:3]),sum(ex[3:]))==(9,9) for ex in reduced)
    checks.append('both_pole2_Griffiths_degrees')
    target=(3,3,3,3,3,3)
    assert reduced=={target:Q(1,24)}
    # A coefficient functional at this monomial kills every multiple of
    # each Fermat Jacobian generator because its relevant exponent is 3<5.
    for i,var in enumerate(s.names):
        expected=tuple(5 if j==i else 0 for j in range(6))
        derivative=s.diff(h if i<3 else c,var)
        assert derivative=={expected:Q(6)}
        assert target[i]<expected[i]
        checks.append('product_Jacobian_functional_annihilates_'+var)
    checks.append('nonzero_product_H02_pairing_1_over_24')

    # On the affine chart the same H,B,C give the actual original cubic.
    affine=Ring(['x','a','y','u','v'])
    vals={var:(affine.const(1) if var in ['t','w'] else affine.var(var)) for var in s.names}
    ha=s.subst(h,vals,affine);ba=s.subst(b,vals,affine);ca=s.subst(c,vals,affine)
    actual=affine.poly('1+x**6+a**6+y**6+(y*u)**6+(y*v)**6+x*y*(y*u)/2+x**3*a*(y*u)*(y*v)/2+x*a*y*(y*v)/3')
    cubic=affine.add(ha,affine.mul(ba,affine.poly('y**2')),affine.mul(ca,affine.poly('y**6')))
    check('actual_immutable_affine_cubic_binding',affine.add(cubic,affine.scale(actual,-1)))
    result={'status':'passed','count':len(checks),'checks':checks,
        'arithmetic':'standard-library Fraction polynomial dictionaries; no primary script imports',
        'finite_connection_data_sha256':hashlib.sha256(finite_path.read_bytes()).hexdigest(),
        'canonical_kappa_matrix':'[[0,3/(4k+27)],[-2,(27-2k)/(4k+27)]]; derivative-of-basis columns',
        'necessary_moment':'B^3 dx da du dv/(H^3 C^2)',
        'projected_numerator':'t^3*x^9*a^3*w^3*u^3*v^3/8',
        'product_H02_pairing':'1/24',
        'scope':'All rational pure-V or pure-W kappa current constraints, including finite algebraic extensions, and relative-closed-time construction lambda wedge eta are obstructed. Any complete coupled current must have divA, A(log kappa), and D(log kappa) not identically zero; divD is unrestricted by this argument. The complete system and arbitrary closed two-form currents remain unexcluded. Hodge/residue/localization implications use classical geometry and are not Lean formalization. No certificate has been found.'}
    Path(__file__).with_name('pure-component-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
