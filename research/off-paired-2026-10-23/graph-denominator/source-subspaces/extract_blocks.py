#!/usr/bin/env python3
"""Extract six homogeneous source-serving blocks from the audited XY assembly."""
from pathlib import Path
import json,struct,hashlib

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent.parent/'graph-assembly'/'assembly-XY-1000003.bin'
meta=json.loads(SOURCE.with_suffix('.json').read_text())
p=meta['prime'];specs=meta['support_specs'];nr=meta['rows'];nc=meta['columns']
rowmaps=[{} for _ in specs]
for r,(s,e) in enumerate(meta['row_exponents']):
    if s<len(specs):rowmaps[s][r]=len(rowmaps[s])
block_index={tuple(spec):i for i,spec in enumerate(specs)}
counts=[0]*len(specs);nonzeros=[0]*len(specs);names=[[] for _ in specs]
paths=[ROOT/f'block-{b}{h}-{p}.bin' for b,h in specs]
outputs=[path.open('wb') for path in paths]
for out in outputs:out.write(b'\0'*16)
with SOURCE.open('rb') as stream:
    assert struct.unpack('<4I',stream.read(16))[:3]==(nr,nc,p)
    for j in range(nc+1):
        n=struct.unpack('<I',stream.read(4))[0]
        pairs=list(struct.iter_unpack('<II',stream.read(8*n)))
        if j==nc:
            assert all(meta['row_exponents'][r][0]==len(specs) for r,v in pairs)
            continue
        name=meta['names'][j];s=block_index[(name[1],name[2])]
        keep=[]
        for r,v in pairs:
            row_support=meta['row_exponents'][r][0]
            assert row_support in (s,len(specs))
            if row_support==s:keep.append((rowmaps[s][r],v))
            else:assert name[0]=='source' and v==1
        outputs[s].write(struct.pack('<I',len(keep)))
        for r,v in keep:outputs[s].write(struct.pack('<II',r,v))
        counts[s]+=1;nonzeros[s]+=len(keep);names[s].append(name)
for s,out in enumerate(outputs):
    out.write(struct.pack('<I',0)) # homogeneous right side
    out.seek(0);out.write(struct.pack('<4I',len(rowmaps[s]),counts[s],p,nonzeros[s]));out.close()
    assert len(names[s])==5315 and all(n[0]=='source' for n in names[s][-24:])
    info={'prime':p,'support':specs[s],'rows':len(rowmaps[s]),'columns':counts[s],
          'numerator_columns':5291,'source_columns':24,'nonzeros':nonzeros[s],
          'source_exponents':meta['source_exponents'],'names':names[s],
          'denominator':meta['denominators'][s],
          'origin_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          'identity':'L_D(N)+Ai*D^2=0 mod F^2; no source-sum rows'}
    paths[s].with_suffix('.json').write_text(json.dumps(info))
print(json.dumps([{'support':specs[s],'rows':len(rowmaps[s]),'columns':counts[s],
                   'nonzeros':nonzeros[s]} for s in range(len(specs))]))
