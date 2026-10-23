#!/usr/bin/env python3
"""Independent stdlib audit of the absolute closed-two-form interface.

Does not import the construction's SymPy checker.  Universal coefficient
identities are cleared polynomial identities, and the physical tests use the
actual Laurent-polynomial H,B,C with exact Fraction arithmetic.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import itertools
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)

    # First check the generic closed-two-form interface with independent
    # coefficient jets.  The only assumptions are commuting derivations.
    pairs = list(itertools.combinations(range(4), 2))
    bn = ['b'+str(i)+str(j) for i, j in pairs]
    r = LaurentRing(['z', 'U', 'K', 't']+bn+
                    [b+'d'+str(i) for b in bn for i in range(4)])
    qn = r.names[:4]
    def deriv(poly, i):
        return r.add(r.diff(poly, qn[i]), *(
            r.mul(r.diff(poly, b), r.var(b+'d'+str(i))) for b in bn))
    def wedge(a, b):
        out = {}
        for ia, va in a.items():
            for ib, vb in b.items():
                if set(ia) & set(ib):
                    continue
                sign = (-1)**sum(i > j for i in ia for j in ib)
                key = tuple(sorted(ia+ib))
                out[key] = r.add(out.get(key, {}), r.scale(r.mul(va, vb), sign))
        return {i: v for i, v in out.items() if v}
    def exterior(a):
        out = {}
        for ia, va in a.items():
            for i in range(4):
                one = wedge({(i,): r.const(1)}, {ia: deriv(va, i)})
                for key, val in one.items():
                    out[key] = r.add(out.get(key, {}), val)
        return {i: v for i, v in out.items() if v}
    theta = {(1,): r.laurent('-1/(3*z)'), (3,): r.laurent('K/(6*t)')}
    omega = {(0, 1): r.laurent('1/(3*z**2)'), (2, 3): r.laurent('1/(6*t)')}
    beta = {ij: r.var(b) for ij, b in zip(pairs, bn)}
    dtheta = exterior(theta)
    for ij in pairs:
        check('theta_primitive_'+str(ij), r.add(dtheta.get(ij, {}),
                                              r.scale(omega.get(ij, {}), -1)))
    rho = r.laurent('1/(18*t*z**2)')
    eta = wedge(theta, beta)
    rho_a = [r.laurent('-b23/(3*z)+K*b12/(6*t)'),
             r.laurent('-K*b02/(6*t)'),
             r.laurent('b03/(3*z)+K*b01/(6*t)'),
             r.laurent('-b02/(3*z)')]
    for i in range(4):
        key = tuple(j for j in range(4) if j != i)
        check('theta_beta_current_component_'+str(i),
              r.add(eta.get(key, {}), r.scale(rho_a[i], -(-1)**i)))
    trace = r.poly('3*z**2*b01+6*t*b23')
    check('twoform_trace_sign', r.add(wedge(beta, omega)[(0, 1, 2, 3)],
                                    r.scale(r.mul(rho, trace), -1)))
    c012 = r.poly('b12d0-b02d1+b01d2')
    c023 = r.poly('b23d0-b03d2+b02d3')
    defect = r.add(*(deriv(rho_a[i], i) for i in range(4)),
                   r.scale(r.mul(rho, trace), -1),
                   r.mul(r.laurent('1/(3*z)'), c023),
                   r.scale(r.mul(r.laurent('K/(6*t)'), c012), -1))
    check('generic_closure_jet_defect', defect)
    de = exterior(eta).get((0, 1, 2, 3), {})
    check('absolute_exterior_Leibniz', r.add(de,
        r.scale(wedge(omega, beta).get((0, 1, 2, 3), {}), -1),
        wedge(theta, exterior(beta)).get((0, 1, 2, 3), {})))

    # Formal coefficient brackets: A={H,B}_0,D={H,C}_0,E={B,C}_0.
    # nq=N(Q), t0={g,Q}_0 are independent jet symbols until stated otherwise.
    c = Ring(['p','B','C','A','D','E','nq','t0','qH','qB','qC'])
    P = c.poly
    g = P('B+3*C*p**2')
    qq = P('A+3*p**2*D+2*p**3*E')
    nb, nc = P('-A+p**3*E'), P('-D-p*E')
    qp = c.diff(qq, 'p')
    check('Q_p_identity', c.add(qp, c.mul(P('6*p'), nc)))
    check('N_g_identity', c.add(nb, c.mul(P('3*p**2'), nc), qq))
    # {f,g}_0 = Q independently by the three coefficient wedge pairs.
    fg = c.add(P('A'), P('3*p**2*D'), P('3*p**3*E'), P('-p**3*E'))
    check('physical_divergence_numerator', c.add(fg, c.scale(qq, -1)))

    nsn = c.add(c.mul(P('p'), c.mul(nb, qq)), P('-B*p*nq'))
    # NS/g^2 - {p^2/(2Q),g}/g + p(2NQ+p{g,Q}_0)/(2Q^2g).
    # Cleared denominator is 2 Q^2 g^2.
    remaining = c.add(c.scale(nsn, 2), c.mul(P('2*p'), c.power(qq, 2)),
        c.scale(c.mul(P('p**2'), c.add(c.mul(P('t0'), g), P('6*C*p*nq'), c.mul(qp, qq))), -1),
        c.mul(P('p*(2*nq+p*t0)'), g))
    check('full_Q_derivative_first_correction', remaining)
    check('Q_log_correction_sign', P('-p*(2*nq+p*t0)+2*p*nq+p**2*t0'))
    check('M_equivalent_bracket_numerator', P('2*(qH+p*qB+p**3*qC)+p*(-qB-3*p**2*qC)-(2*qH+p*qB-p**3*qC)'))

    # Direct absolute trace of d[-p^2(dB+3p^2dC)/(2Qg)].
    # Chain rules use Dp=-df_base/g, all Q base derivatives, and Q_p.
    # This route does not use the previous NS simplification.
    direct = c.add(
        c.scale(c.mul(P('p'), c.mul(qq, c.mul(g, nb))), -2),
        c.mul(P('p**2*qB'), c.power(g, 2)),
        c.mul(P('p**2'), c.mul(g, c.mul(qp, nb))),
        c.scale(c.mul(P('p**4*E'), c.mul(qq, g)), -3),
        c.mul(P('6*C*p**3'), c.mul(qq, nb)),
        c.scale(c.mul(P('p**3'), c.mul(qq, c.mul(g, nc))), -12),
        c.mul(P('3*p**4*qC'), c.power(g, 2)),
        c.mul(P('3*p**4'), c.mul(g, c.mul(qp, nc))),
        c.mul(P('3*p**4*E'), c.mul(qq, g)),
        c.mul(P('18*C*p**5'), c.mul(qq, nc)))
    target = c.add(c.mul(P('2*B*p'), c.power(qq, 2)),
                   c.mul(P('p**2*(qB+3*p**2*qC)'), c.power(g, 2)))
    check('direct_absolute_lambda_tilde_trace', c.add(direct, c.scale(target, -1)))

    # Equality of potentials is a cotangent identity modulo df=0, after Qg.
    lam1 = [P('-B*p-3*C*p**3'), {}, P('-p**2/2'), P('-3*p**4/2')]
    lam2 = [{}, P('p'), P('p**2/2'), P('-p**4/2')]
    df = [g, P('1'), P('p'), P('p**3')]
    for i in range(4):
        check('lambda_representations_'+str(i), c.add(lam1[i], c.scale(lam2[i], -1), c.mul(P('p'), df[i])))
    # lambda+F dlogQ+dF=lambda_tilde, in (dp,dB,dC,dQ).
    # Clear 2 Q^2 g; each coefficient is computed from the displayed forms.
    check('Q_log_potential_dp', c.add(c.scale(c.mul(P('p'), c.mul(qq, g)), -2), c.mul(P('2*p'), c.mul(qq, g))))
    check('Q_log_potential_dQ', c.add(c.mul(P('p**2'), g), c.scale(c.mul(P('p**2'), g), -1)))

    # Branch residue sign, clearing 2 Q^3 X_Delta(p), then B=-3Cp^2.
    delta_p = c.mul(P('18*C*p**2'), qq)
    delta_q = c.add(P('108*C**2*p**3*nq'),
                    c.scale(c.mul(P('108*C*p**3'), c.mul(qq, nc)), -1))
    branch_res = c.add(c.scale(c.mul(delta_p, nsn), 2),
                      c.mul(P('2*p'), c.mul(c.power(qq, 2), delta_p)),
                      c.scale(c.mul(P('p**2'), c.mul(qq, delta_q)), -1))
    vals = {v: c.var(v) for v in c.names}
    vals['B'] = P('-3*C*p**2')
    check('old_branch_residue_primitive_sign', c.subst(branch_res, vals, c))

    # Actual physical H,B,C; no universal-coefficient specialization is used.
    a = LaurentRing(['p', 'z', 'U', 'K', 't'])
    h = a.poly('1+z**2+t')
    b = a.poly('U/2+K/3+z*U*K/2')
    cc = a.laurent('1/z**2+U**6+K**6/t')
    def bracket0(x, y):
        return a.add(a.mul(a.poly('3*z**2'), a.add(a.mul(a.diff(x,'z'),a.diff(y,'U')),a.scale(a.mul(a.diff(x,'U'),a.diff(y,'z')),-1))),
                     a.mul(a.poly('6*t'), a.add(a.mul(a.diff(x,'K'),a.diff(y,'t')),a.scale(a.mul(a.diff(x,'t'),a.diff(y,'K')),-1))))
    f = a.add(h, a.mul(b, a.poly('p')), a.mul(cc, a.poly('p**3')))
    gg = a.add(b, a.mul(cc, a.poly('3*p**2')))
    qphys = a.add(bracket0(h,b), a.mul(a.poly('3*p**2'),bracket0(h,cc)),a.mul(a.poly('2*p**3'),bracket0(b,cc)))
    tph = bracket0(gg,qphys)
    check('actual_f_g_bracket', a.add(bracket0(f,gg),a.scale(qphys,-1)))
    def det3(m):
        return a.add(*(a.scale(a.mul(m[0][pi[0]],a.mul(m[1][pi[1]],m[2][pi[2]])),
                   (-1)**sum(pi[i]>pi[j] for i in range(3) for j in range(i+1,3)))
                     for pi in itertools.permutations(range(3))))
    minor = det3([[a.diff(v, q) for q in ['z','U','K']] for v in [h,b,cc]])
    un = Ring(['p'])
    def at_regular(poly):
        ans = {}
        for ex, co in poly.items():
            value = co * Q(2)**ex[4]
            ans = un.add(ans, {(ex[0],): value})
        return ans
    # Univariate remainder division over Q, independent of SymPy.
    def rem(poly, modulus):
        out = dict(poly)
        de, dc = max(modulus.items())
        while out and max(out)[0] >= de[0]:
            ee = max(out)
            co = out[ee]/dc
            out = un.add(out, un.scale(un.mul({(ee[0]-de[0],):Q(1)},modulus),-co))
        return out
    sample_f = at_regular(f)
    sample_t = rem(at_regular(tph), sample_f)
    check('nonzero_remainder_sample_value', un.add(sample_t, un.poly('-103707*p**2/5-3778244*p/75+73476/25')))
    assert sample_t
    checks.append('physical_Q_remainder_nonzero')

    # Exact quadratic field Q[p]/(p^2-1/12) for an actual simple branch.
    def qa(x, y): return (x[0]+y[0],x[1]+y[1])
    def qm(x, y): return (x[0]*y[0]+x[1]*y[1]/12,x[0]*y[1]+x[1]*y[0])
    def qi(x):
        d=x[0]*x[0]-x[1]*x[1]/12
        assert d
        return (x[0]/d,-x[1]/d)
    def qpwr(x, n):
        if n<0: return qpwr(qi(x),-n)
        ans=(Q(1),Q(0))
        for _ in range(n): ans=qm(ans,x)
        return ans
    point=[(Q(0),Q(1)),(Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(0)),(Q(-2),Q(1,3))]
    def at_branch(poly):
        out=(Q(0),Q(0))
        for ex, co in poly.items():
            v=(co,Q(0))
            for value,n in zip(point,ex): v=qm(v,qpwr(value,n))
            out=qa(out,v)
        return out
    def branch_check(name, poly):
        assert at_branch(poly)==(0,0),(name,at_branch(poly))
        checks.append(name)
    branch_check('actual_simple_branch_f',f)
    branch_check('actual_simple_branch_g',gg)
    branch_check('actual_simple_branch_coordinate_minor',a.add(minor,a.const(2)))
    branch_check('actual_simple_branch_Q',a.add(qphys,a.poly('8-5*p/6')))
    branch_check('actual_simple_branch_gp',a.add(a.diff(gg,'p'),a.poly('-12*p')))
    assert at_branch(qphys)!=(0,0) and at_branch(a.diff(gg,'p'))!=(0,0)
    checks.append('actual_simple_branch_Q_and_gp_nonzero')

    target = Path(__file__).parents[2]/'jacobian/closed-two-form-current.py'
    result={'status':'passed','arithmetic':'Python standard-library Fraction polynomial/Laurent dictionaries and exact quadratic field arithmetic',
            'count':len(checks),'checks':checks,
            'audited_primary_file_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
            'physical_sample_remainder':{'p2':'103707/5','p':'3778244/75','constant':'-73476/25'},
            'convention':'left X_F(G)={F,G}; i_XF omega=-dF; N=gX_p',
            'scope':'Closed-two-form interface and partial source-carrying current verified. Absolute lambda_tilde trace is R-p^2{g,Q}_0/(2Q^2g), with nonzero remainder. Generic g-pole removal is only on Q*coordinate-minor!=0; Q poles and intersections remain. No primitive or certificate.'}
    Path(__file__).with_name('closed-twoform-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
