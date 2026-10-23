#!/usr/bin/env python3
"""Independent compact-formula and Fraction spot audit of source-bound H_N.

The primary exact QQ(u)[w] Hermite program is not imported or rerun. This
checks its literal moment split as a polynomial identity and its serialized
primitive derivatives against independently assembled source formulas.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring
import verify_actual_lifts_fraction as jt
jt.ORDER=3


def main():
    checks=[]
    def check(name,x):
        assert not x,(name,x)
        checks.append(name)
    r=Ring(['i','u','w']);p=r.poly
    T=p('1+w**3');N=r.add(p('9*w**2'),r.scale(r.mul(p('u'),T),-16))
    L=r.add(r.scale(r.mul(r.power(T,5),N),256),p('729*i**6*u*w**6'))
    left=r.add(r.mul(r.add(r.mul(T,L),r.scale(r.mul(p('w'),r.mul(L,r.diff(T,'w'))),2),r.scale(r.mul(p('w'),r.mul(T,r.diff(L,'w'))),-1)),N),
               r.mul(p('w'),r.mul(T,r.mul(L,r.diff(N,'w')))))
    right=r.add(r.mul(r.scale(r.mul(r.power(T,5),r.mul(N,p('1-8*w**3'))),256),N),
                r.mul(p('729*i**6*u'),r.add(r.mul(p('w**9-5*w**6'),N),r.mul(p('w**7'),r.mul(T,r.diff(N,'w'))))))
    check('exact global split of tLift dlogv',r.add(left,r.scale(right,-1)))
    base=HERE.parents[1]/'coupled-fresh'
    source_path=base/'genus4-gm-independent/cubic-residue-potentials-results.json'
    primitive_path=base/'ruling-source/adjoint-reconstruction/n-only-hermite-results.json'
    source_raw=source_path.read_bytes();primitive_raw=primitive_path.read_bytes()
    packet=json.loads(source_raw)['actual_Ssrc_residue'];primitive=json.loads(primitive_raw)
    values=[]
    for u0,w0 in [(Q(1,4),Q(1)),(Q(1),Q(2)),(Q(2),Q(1,2)),(Q(1,3),Q(3))]:
        u=jt.variable(u0,0);w=jt.variable(w0,1);T=1+w**3;N=9*w*w-16*u*T;Nw=18*w-48*u*w*w
        env=dict(u=u)
        def array(coeff):return sum((jt.evaluate(x,env)*w**j for j,x in enumerate(coeff)),jt.Jet())
        f=array(packet['PE_residue_f_coefficients']);g=array(packet['PD_residue_g_coefficients']);crt=array(packet['CRT_factor_coefficients'])
        ah=54*w*T/(u*N);af=f*Nw/N;ag=g*Nw/N
        pm=256*crt*T**5*N*(1-8*w**3)
        rp=729*u*crt*(w**9-5*w**6+w**7*T*Nw/N)
        def th(x):return u*x.partial(0)
        def chain(x,factors):
            for a,b in factors:x=a*x+b*th(x)
            return x
        source={
          'i^-1':chain(ah-af,[(2,2),(3,2)])+2*th(th(ag)+ag)-chain(rp,[(2,-2),(1,-2),(0,-2)]),
          'i^-2':chain(af,[(1,2),(3,1)])-(4*th(th(ag))-2*th(ag))/u,
          'i^-7':-chain(pm,[(-4,-2),(-5,-2),(-6,-2)])}
        vals={}
        for label,component in primitive['components'].items():
            HN=array(component['polynomial_primitive_coefficients'])
            for term in component['proper_primitive_terms']:
                HN=HN+array(term['numerator_coefficients'])/N**term['denominator_power']
            actual=HN.partial(1).value;expected=source[label].value
            check(f'u={u0},w={w0}: literal derivative {label}',actual-expected)
            vals[label]=str(expected)
        values.append({'u':str(u0),'w':str(w0),'source_component_values':vals})
    assert source_path.read_bytes()==source_raw and primitive_path.read_bytes()==primitive_raw
    out={'status':'passed','count':len(checks),'checks':checks,'exact_points':values,
        'method':'independent cleared polynomial dlog moment split and Fraction third Taylor derivatives of actual forced-source formulas; no primary code imported',
        'source_packet_sha256':hashlib.sha256(source_raw).hexdigest(),
        'primitive_packet_sha256':hashlib.sha256(primitive_raw).hexdigest(),
        'scope':'Checks compact K construction and serialized H_N derivative identities at four exact generic points. The primary QQ(u)[w] global identities were inspected, not independently reimplemented. Full Cartan corrections remain explicit; K(B0-1/2)chi is still unserved.'}
    (HERE/'n-only-hermite-fraction-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('checks','exact_points')},indent=2))


if __name__=='__main__':main()
