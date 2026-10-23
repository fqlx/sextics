#!/usr/bin/env python3
"""Target/hash and fixed-coordinate scope audit of the downloaded public packet.

This does not reimplement the contributor's five large rank calculations.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast
import base64
import gzip
import hashlib
import itertools
import json
import shutil
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring


def main():
    root=Path('/workspace/off-paired-public-quotient-obstructions')
    manifest=json.loads((root/'download-sha256.json').read_text())
    for name,want in manifest.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==want,name
    bundle=json.loads(gzip.decompress(base64.b64decode((root/'bounded_certificate_bundle.json.gz.b64').read_bytes())))
    raw=bundle['target_record'].encode()
    assert hashlib.sha256(raw).hexdigest()==bundle['target_sha256']
    def fields(raw):return dict(line.split(': ',1) for line in raw.decode().splitlines() if line.startswith(('F: ','A: ','q: ')))
    r=Ring(['X0','X1','X2','Y0','Y1','Y2']);want=fields(raw)
    hashes={}
    for name,path in [('current','/workspace/off-paired-sextics/data/off-paired/instance.rec'),('original','/workspace/sextics/data/off-paired/instance.rec')]:
        live=Path(path).read_bytes();ff=fields(live)
        assert Q(ff['q'])==Q(want['q'])==1
        assert all(r.poly(ff[k])==r.poly(want[k]) for k in ['F','A'])
        hashes[name]=hashlib.sha256(live).hexdigest()
    # Read only literal polynomial data, without executing the contributor.
    tree=ast.parse((root/'verify_coordinate_threefolds.py').read_text())
    def literal(n):
        if isinstance(n,ast.Constant):return n.value
        if isinstance(n,ast.Tuple):return tuple(literal(e) for e in n.elts)
        if isinstance(n,ast.Dict):return {literal(k):literal(v) for k,v in zip(n.keys,n.values)}
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -literal(n.operand)
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='F':return Q(*(literal(e) for e in n.args))
        raise ValueError(ast.dump(n))
    vals={}
    for node in tree.body:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in ['PHYSICAL','G','E','SOURCE']:
            vals[node.targets[0].id]=literal(node.value)
    phys=Ring(['x','y','z','a','b'])
    subs=dict(zip(r.names,[phys.const(1),phys.var('x'),phys.var('a'),phys.var('y'),phys.var('z'),phys.var('b')]))
    assert r.subst(r.poly(want['F']),subs,phys)==vals['PHYSICAL']
    assert r.subst(r.poly(want['A']),subs,phys)==phys.poly('y**3')
    E=vals['E']
    det=sum((-1)**sum(pm[i]>pm[j] for i in range(5) for j in range(i+1,5))*__import__('functools').reduce(lambda a,b:a*b,[E[i][pm[i]] for i in range(5)],1) for pm in itertools.permutations(range(5)))
    assert det==36
    pull=lambda e:tuple(sum(e[j]*E[j][i] for j in range(5)) for i in range(5))
    assert {pull(e):c for e,c in vals['G'].items()}==vals['PHYSICAL']
    assert pull(vals['SOURCE'])==(1,4,1,1,1)
    # Preserve every downloaded file. The unchanged standalone contributor
    # checker writes its result relative to __file__, so run a byte-for-byte
    # copy in the audit-owned directory instead.
    script=root/'verify_coordinate_threefolds.py';copy=HERE/script.name
    shutil.copyfile(script,copy)
    assert copy.read_bytes()==script.read_bytes()
    meta=json.loads((root/'gist-metadata.json').read_text())
    result={'manifest_entries_verified':len(manifest),'gist_url':meta['html_url'],'gist_version':meta['history'][0]['version'],'gist_updated_at':meta['updated_at'],
        'target_raw_hashes':hashes,'packet_target_sha256':bundle['target_sha256'],'target_polynomial_and_q_equality':'passed with safe AST/Fraction polynomial parsing, including original rendering',
        'physical_checker_literal_matches_actual_target':True,'quotient_log_Jacobian_determinant':det,'source_exponent_pullback':[1,4,1,1,1],
        'contributor_checker_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),
        'verification_kind':'Independent target/hash/scope inspection; rank arithmetic will be a rerun of the unchanged contributor checker, not an independent implementation or Lean proof.'}
    (HERE/'inspection-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
