#!/usr/bin/env python3
"""Check every projected source lift against the original extracted block."""
from pathlib import Path
import json,struct,sys
sys.path.insert(0,'/workspace/off-paired-research-published')
from ansatz import F,der,scl,Q
ROOT=Path(__file__).resolve().parent
reports=[]
for path in sorted(ROOT.glob('block-*.bin')):
    meta=json.loads(path.with_suffix('.json').read_text())
    result=json.loads(path.with_suffix('.projection.json').read_text())
    p=meta['prime'];n=meta['columns'];sources=[tuple(e) for e in meta['source_exponents']]
    basis=result['source_basis'];lifts=[dict(v) for v in result['kernel_lifts']]
    assert len(basis)==len(lifts)==result['served_source_dimension']
    assert result['kernel_dimension']==n-result['rank']
    expected=[]
    for coord,other,scale in [(4,0,Q(1,6)),(0,4,Q(3,2))]:
        poly={tuple(e[j]+(j==other) for j in range(6)):c*scale for e,c in der(F,coord).items()}
        expected.append([poly.get(e,Q(0)).numerator*pow(poly.get(e,Q(0)).denominator,-1,p)%p for e in sources])
    assert basis==expected
    for row,lift in zip(basis,lifts):
        assert [lift.get(n-24+j,0) for j in range(24)]==row
    with path.open('rb') as stream:
        nr,nc,prime,nnz=struct.unpack('<4I',stream.read(16));assert (nc,prime)==(n,p)
        residual=[[0]*nr for _ in lifts]
        for j in range(nc+1):
            sz=struct.unpack('<I',stream.read(4))[0]
            pairs=list(struct.iter_unpack('<II',stream.read(8*sz)))
            if j==nc:assert not pairs;continue
            for lift,out in zip(lifts,residual):
                if j in lift:
                    a=lift[j]
                    for r,c in pairs:out[r]=(out[r]+a*c)%p
        assert all(not any(out) for out in residual)
    reports.append({'support':meta['support'],'prime':p,'rank':result['rank'],
                    'kernel_dimension':result['kernel_dimension'],
                    'served_source_dimension':len(basis),'all_lifts_substitute_to_zero':True,
                    'basis_matches_exact_universal_sources':True,
                    'seconds':result['seconds'],'peak_rss_mb':result['peak_rss_mb']})
out={'status':'passed','sources':['X0*(partial F/partial Y1)/6','3*Y1*(partial F/partial X0)/2'],
     'scope':'modular projected kernel of six fixed homogeneous block systems; no characteristic-zero upper dimension claim',
     'blocks':reports}
(ROOT/'projection-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
