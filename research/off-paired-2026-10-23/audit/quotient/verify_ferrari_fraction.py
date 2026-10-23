#!/usr/bin/env python3
"""Independent exact normal-jet and Ferrari residue reconstruction audit."""
from pathlib import Path
from fractions import Fraction as Q
import sys
import json
import hashlib
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from verify_connection_fraction import Ring
sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_piola_transfer import LaurentRing


def monic_first_variable_remainder(ring, polynomial, divisor, degree):
    leading = (degree,) + (0,) * (len(ring.names)-1)
    assert divisor.get(leading) == 1
    result = dict(polynomial)
    while result:
        e = max(result)
        if e[0] < degree:
            break
        term = {tuple(a-b for a, b in zip(e, leading)): result[e]}
        result = ring.add(result, ring.scale(ring.mul(term, divisor), -1))
    return result


def main():
    checks = []
    def check(name, residual):
        assert not residual, (name, residual)
        checks.append(name)
    # The toric normal derivation is checked before setting F=0.
    n = Ring(['u', 'v', 'w', 'S', 'e'])
    F = n.poly('v**2+w**2+e*w+S')
    J2 = n.poly('2*v**2-2*w**2-e*w')
    J0 = n.poly('4*v**2+e*w+2*S')
    toric = n.poly('u**3-v*w')
    G = n.poly('v**4+S*v**2+e*u**3*v+u**6')
    def delta_numerator(poly):
        return n.add(n.mul(n.var('v'), n.diff(poly, 'v')),
                     n.scale(n.mul(n.var('w'), n.diff(poly, 'w')), -1))
    check('toric_normal_F', n.add(delta_numerator(F), n.scale(J2, -1)))
    check('toric_normal_relation', delta_numerator(toric))
    check('toric_second_normal_jet', n.add(J2, n.scale(J0, -1), n.scale(F, 2)))
    # delta_F(v/J2) is this expression divided by J2^3.
    numerator = n.add(n.mul(n.var('v'), J2), n.scale(n.mul(n.var('v'), delta_numerator(J2)), -1))
    target_num = n.poly('v*(4*v**2+4*e*w+6*S)')
    check('toric_actual_second_residue', n.add(numerator, n.scale(target_num, -1), n.scale(n.mul(n.var('v'), F), 6)))
    Gv, Gvv = n.diff(G, 'v'), n.diff(n.diff(G, 'v'), 'v')
    residue_num = n.add(n.scale(n.mul(n.poly('v**3'), Gv), 4),
                       n.scale(n.mul(n.poly('v**4'), Gvv), -1))
    residual = n.add(n.mul(residue_num, n.power(J0, 3)),
                     n.scale(n.mul(target_num, n.power(Gv, 3)), -1))
    check('quartic_and_toric_residue_agree', monic_first_variable_remainder(n, residual, toric, 3))

    # Ferrari factorization with all denominators retained.
    f = LaurentRing(['v', 'u', 'S', 'e', 'q'])
    r0 = f.laurent('(S+q**2-e*u**3/q)/2')
    s0 = f.laurent('(S+q**2+e*u**3/q)/2')
    AA = f.add(f.poly('v**2+q*v'), r0)
    BB = f.add(f.poly('v**2-q*v'), s0)
    GG = f.poly('v**4+S*v**2+e*u**3*v+u**6')
    resolvent = f.poly('q**6+2*S*q**4+(S**2-4*u**6)*q**2-e**2*u**6')
    check('Ferrari_factorization_resolvent', f.add(
        f.mul(f.poly('4*q**2'), f.add(f.mul(AA, BB), f.scale(GG, -1))),
        f.scale(resolvent, -1)))
    conic = LaurentRing(['e', 'tau'])
    qparam = conic.laurent('e*(tau-1/tau)/4')
    kparam = conic.laurent('e*(tau+1/tau)/2')
    check('Ferrari_resolvent_conic', conic.add(conic.power(kparam, 2),
             conic.scale(conic.power(qparam, 2), -4), conic.poly('-e**2')))

    geometry = Path(__file__).resolve().parent.parent.parent/'quotient_geometry'
    generic_path = geometry/'ferrari-trace.json'
    generic = json.loads(generic_path.read_text())
    invariant_path = geometry/'ferrari-invariant-source.json'
    invariant = json.loads(invariant_path.read_text())

    def audit_reconstruction(ring, variable, qa, ra, sa, data, denominator, label):
        v = ring.var(variable)
        A = ring.add(ring.power(v, 2), ring.mul(qa, v), ra)
        B = ring.add(ring.power(v, 2), ring.scale(ring.mul(qa, v), -1), sa)
        G = ring.mul(A, B)
        Gv = ring.diff(G, variable)
        Gvv = ring.diff(Gv, variable)
        source_num = ring.add(ring.scale(ring.mul(ring.power(v, 3), Gv), 4),
                              ring.scale(ring.mul(ring.power(v, 4), Gvv), -1))
        source_den = ring.scale(ring.power(Gv, 3), 3)
        L = ring.poly(denominator)
        tr = ring.cleared(data['trace'], L)
        odd_key = 'delta_coefficient' if 'delta_coefficient' in data else 'anti_delta_coefficient'
        odd = ring.cleared(data[odd_key], L)
        candidate_num = ring.add(ring.scale(tr, Q(1, 2)),
            ring.mul(odd, ring.add(ring.scale(v, 2), qa)))
        residual = ring.add(ring.mul(source_num, L),
                            ring.scale(ring.mul(source_den, candidate_num), -1))
        check(label+'_residue_reconstruction', monic_first_variable_remainder(ring, residual, A, 2))
        assert odd, label+' trace-zero component must not vanish'
        checks.append(label+'_trace_zero_part_nonzero')
        # The other root is -qa-v, so the trace of the displayed delta
        # component is identically zero, without any numerical specialization.
        check(label+'_quadratic_trace', ring.add(
            ring.mul(odd, ring.add(ring.scale(v, 2), qa)),
            ring.mul(odd, ring.add(ring.scale(ring.add(ring.scale(qa, -1), ring.scale(v, -1)), 2), qa))))

    gr = Ring(['v', 'q', 'r', 's'])
    audit_reconstruction(gr, 'v', gr.var('q'), gr.var('r'), gr.var('s'), generic,
        '3*(q**2-4*r)**2*(2*q**2*r+2*q**2*s+r**2-2*r*s+s**2)**3', 'generic_Ferrari')
    ir = Ring(['V', 'e', 'rho', 'h'])
    audit_reconstruction(ir, 'V', ir.poly('e/4'), ir.poly('(rho-2)*h'),
        ir.poly('(rho+2)*h'), invariant,
        '3*(e**2*rho+64*h)**3*(e**2-64*h*rho+128*h)**2', 'invariant_Ferrari')

    # Normalized Ferrari variables: v=dV, u=dU, d^2=rho^2-4.
    # The scalar second-pole residue scales by d^-3. Three changing base
    # coordinates (u,z,b) supply d^3, leaving the horizontal dlog(d) terms.
    scaling = LaurentRing(['d', 'rho'])
    assert scaling.diff(scaling.poly('rho**2-4'), 'rho') == scaling.poly('2*rho')
    checks.append('invariant_horizontal_log_derivative_rho_over_d2')
    result = {
        'status': 'passed', 'arithmetic': 'standard-library Fraction polynomial dictionaries',
        'checks': checks,
        'data_hashes': {generic_path.name: hashlib.sha256(generic_path.read_bytes()).hexdigest(),
                        invariant_path.name: hashlib.sha256(invariant_path.read_bytes()).hexdigest()},
        'normal_jet': 'J2=J0-2F retained before differentiating; replacement by J0 is only on F=0',
        'trace_scope': 'Both trace and nonzero trace-zero delta component reconstruct the actual scalar second-pole residue',
        'orientation': 'For source du∧dv∧dz∧da∧db and normal differential dG first, physical residue is -r du∧dz∧da∧db. Positive r denotes the relative one-variable residue or the opposite base orientation.',
        'source_scaling': 'Under v=dV,u=dU,z=dZ,b=dB, scalar residue scales d^-3 and base volume d^3; dlog d=rho/(rho^2-4) d rho must remain.',
        'scope': 'Exact scalar normal/source/trace audit; no global primitive, descent, or certificate follows.'
    }
    path = Path(__file__).with_name('ferrari-fraction-results.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
