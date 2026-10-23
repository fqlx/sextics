#!/usr/bin/env python3
"""Independent integrity/target/algebra audit of 2026-10-22 public packet.

Imports only the independent audit's stdlib polynomial Ring, not any public
packet generator or checker. Classical geometric implications are reviewed
in PUBLIC-CONTACT-AUDIT.md, not claimed as kernel formalization here.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import zipfile
from verify_connection_fraction import Ring, record


def main():
    packet_root=Path('/workspace/off-paired-contact-public-2026-10-22')
    base=packet_root/'off-paired-contact-obstruction-2026-10-22'
    current=Path('/workspace/off-paired-sextics/data/off-paired/instance.rec')
    original=Path('/workspace/sextics/data/off-paired/instance.rec')
    checks=[]
    def check(name,residual):
        assert not residual,(name,residual)
        checks.append(name)
    ziphash=hashlib.sha256((packet_root/'packet.zip').read_bytes()).hexdigest()
    assert ziphash=='06ee0fdf55a3a5a2d82d5d0293df850220eb7afa1fe5fbe96f9b80a656fc31de'
    checks.append('downloaded_zip_expected_hash')
    listed={}
    for line in (base/'SHA256SUMS').read_text().splitlines():
        digest,rel=line.split('  ',1)
        assert rel not in listed and not Path(rel).is_absolute() and '..' not in Path(rel).parts
        assert hashlib.sha256((base/rel).read_bytes()).hexdigest()==digest,rel
        listed[rel]=digest
    actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
    assert set(listed)==actual-{'SHA256SUMS'}
    checks.append('complete_manifest_all_'+str(len(listed))+'_files')
    with zipfile.ZipFile(packet_root/'packet.zip') as zf:
        for member in zf.infolist():
            if member.is_dir():continue
            rel=Path(member.filename).relative_to(base.name)
            assert zf.read(member)==(base/rel).read_bytes(),member.filename
    checks.append('unpacked_files_equal_zip_entries')

    physical=Ring(['X0','X1','X2','Y0','Y1','Y2'])
    expectedF=physical.poly('X0**6+X1**6+X2**6+Y0**6+Y1**6+Y2**6+X0**3*X1*Y0*Y1/2+X1**3*X2*Y1*Y2/2+X0**2*X1*X2*Y0*Y2/3')
    expectedA=physical.poly('X0**3*Y0**3')
    hashes={}
    for label,path in [('live21',current),('original',original),('public_packet',base/'target/instance.rec')]:
        raw,fields=record(path)
        assert fields['q']=='1'
        check('target_F_'+label,physical.add(physical.poly(fields['F']),physical.scale(expectedF,-1)))
        check('target_A_'+label,physical.add(physical.poly(fields['A']),physical.scale(expectedA,-1)))
        hashes[label]=hashlib.sha256(raw).hexdigest()
    target_json=json.loads((base/'TARGET.json').read_text())
    assert target_json['source_commit']=='21fccb6b4f1d4070ddaa30195a78f268247569e6'
    assert target_json['q']==1 and target_json['variable_order']==list(physical.names)
    check('TARGET_json_F',physical.add(physical.poly(target_json['F']),physical.scale(expectedF,-1)))
    check('TARGET_json_A',physical.add(physical.poly(target_json['A']),physical.scale(expectedA,-1)))
    assert target_json['instance_rec_sha256']==hashes['live21']==hashes['public_packet']
    checks.append('TARGET_json_snapshot_hash')
    canonical={'variables':list(physical.names),'q':1,
               'F':[[list(e),co.numerator,co.denominator] for e,co in sorted(expectedF.items())],
               'A':[[list(e),co.numerator,co.denominator] for e,co in sorted(expectedA.items())]}
    canonical_json=json.dumps(canonical,sort_keys=True,separators=(',',':'))

    data=json.loads((base/'contact_obstruction.json').read_text())
    r=Ring(['w','x','y','z'])
    assert data['variables']==list(r.names)
    def decode(terms):
        out={}
        for term in terms:
            ex=tuple(term['exponents']);co=Q(term['coefficient'])
            assert len(ex)==4 and all(type(i) is int and i>=0 for i in ex)
            assert ex not in out,'duplicate exported monomial'
            if co:out[ex]=co
        return out
    h=r.poly('w**6+x**6+y**6+z**6+w**3*x*y*z/2')
    c=r.poly('x**3*z/2+w**2*x*y/3')
    a=r.poly('w**3*y**3')
    check('exported_contact_H',r.add(decode(data['H']),r.scale(h,-1)))
    full=r.mul(a,r.power(c,5))
    invariant={ex:co for ex,co in full.items() if (ex[1]-ex[3])%6==0 and (ex[2]-ex[3])%6==0}
    check('actual_source_invariant_projection',r.add(invariant,r.poly('-5*w**11*x**7*y**7*z/162')))
    check('exported_source',r.add(decode(data['projected_source']),r.scale(invariant,-1)))
    grad=[r.diff(h,v) for v in r.names]
    source=invariant
    for pole,step in zip([5,4],data['steps'],strict=True):
        assert pole==step['pole']
        check('source_at_pole_'+str(pole),r.add(decode(step['source']),r.scale(source,-1)))
        multipliers=[decode(v) for v in step['multipliers']]
        assert len(multipliers)==4
        check('full_Jacobian_lift_pole_'+str(pole),r.add(source,r.scale(r.add(*(r.mul(m,g) for m,g in zip(multipliers,grad))),-1)))
        source=r.scale(r.add(*(r.diff(m,v) for m,v in zip(multipliers,r.names))),Q(1,pole-1))
        check('reduced_source_pole_'+str(pole),r.add(source,r.scale(decode(step['reduced']),-1)))
        assert all(sum(ex)==6*(pole-1)-4 for ex in source)
    functional=decode(data['cokernel_witness'])
    assert len(functional)==20 and all(sum(ex)==14 for ex in functional)
    def pair(poly):return sum((co*functional.get(ex,Q(0)) for ex,co in poly.items()),Q(0))
    count=0
    for iw in range(10):
        for ix in range(10-iw):
            for iy in range(10-iw-ix):
                iz=9-iw-ix-iy
                mon={(iw,ix,iy,iz):Q(1)}
                for g in grad:
                    assert pair(r.mul(mon,g))==0
                    count+=1
    assert count==880
    checks.append('all_880_full_Jacobian_generator_multiples')
    pairing=pair(source)
    assert pairing==Q(data['pairing'])==Q(-54190940,990659911761)
    checks.append('nonzero_actual_source_pairing')
    last=[decode(v) for v in data['final_jacobian_multipliers']]
    remainder=decode(data['final_remainder'])
    assert remainder=={(2,4,4,4):pairing}
    check('final_explicit_Jacobian_lift',r.add(source,r.scale(remainder,-1),r.scale(r.add(*(r.mul(m,g) for m,g in zip(last,grad))),-1)))

    # Universal integrating-factor identity, before imposing either equation.
    u=Ring(['H','C','VH','VC','divV'])
    check('integrating_factor_m2_universal_identity',u.poly('C**6*H*divV+6*C**5*H*VC-4*C**6*VH-(C**6*H*divV-2*C**5*(2*C*VH-3*H*VC))'))
    # The broad strict current coefficient comparison after its forced
    # equalities f=g=h, divP=4h, PC=4Ch, PH=A+6Hh.
    v=Ring(['a','b','H','C','A','h'])
    strict=v.poly('6*h*a**6+6*h*b**6+(4*C*h+2*C*h)*a*b+(A+6*H*h)-(a**6+b**6+C*a*b+H)*(4*h+2*h)-A')
    check('broader_old_fiber_shape_forced_contact_relation',strict)
    nine=json.loads((base/'genus2_current_search_all_QQ.json').read_text())
    assert len(nine)==9 and all(d['p']==0 and d['augmented_rank']==d['rank']+1 and not d['candidate'] for d in nine)
    result={'status':'passed','checks':checks,'count':len(checks),'arithmetic':'Independent standard-library Fraction polynomial dictionaries; no public checker/generator imports',
        'packet_zip_sha256':ziphash,'manifest_file_count':len(listed),'target_raw_sha256':hashes,
        'canonical_target_sha256':hashlib.sha256(canonical_json.encode()).hexdigest(),
        'canonical_target_serialization':'UTF-8 json.dumps(target,sort_keys=True,separators=(comma,colon)), no trailing newline. F,A arrays of [lexicographic exponent vector,numerator,denominator]; immutable variable order.',
        'pairing':str(pairing),'jacobian_relations_checked':count,
        'nine_bounded_results_read_only':[{'D':d['D'],'rank':d['rank'],'augmented_rank':d['augmented_rank']} for d in nine],
        'scope':'Obstructs only old 3-base divergence-free contact current, its stated affine-linear old fiber shapes, and finite algebraic extensions thereof. Does not automatically obstruct new 4-base cubic-ray complete rank2 currents. Nine old bounded endpoint searches were read, not rerun. Geometric localization/residue input is classical, not Lean verification. No certificate has been found.'}
    Path(__file__).with_name('public-contact-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
