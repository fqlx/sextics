#!/usr/bin/env python3
"""Development compilation/replay for PR 221; this does not grant acceptance.

Run the unchanged protected sandbox compiler and axiom audit on the active
entry-point dependency closure. Unlike a solve submission, the development
harness deliberately reaches the compiler even when a known admission is
present, so it can diagnose helper errors. The unchanged final axiom audit
must still reject sorryAx. No protected checker file or policy is changed.
"""
import hashlib
import json
from pathlib import Path
import sys
import traceback

import yaml

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / 'scripts' / 'proposals'))
from sandbox import verify

folder = root / 'data' / 'cycle-q2'
order = ['Workspace.lean', 'GeometricTarget.lean', 'GeometricSeed.lean', 'Solution.lean']
files = {name: (folder / name).read_bytes() for name in order}
files['proof.json'] = (folder / 'proof.json').read_bytes()
instance = yaml.safe_load((folder / 'instance.rec').read_text())
manifest = json.loads(files['proof.json'])
policy = json.loads((root / '.github' / 'solve-policy.json').read_text())
out = root / 'development-receipts'
out.mkdir(exist_ok=True)
record = {
  'purpose': 'DEVELOPMENT_ONLY_NOT_PROTECTED_ACCEPTANCE',
  'source_sha256': {k: hashlib.sha256(v).hexdigest() for k, v in files.items()},
  'active_modules': order,
  'certificate_accepted': False,
}
try:
    result = verify(root, files, instance, manifest, order, [], policy, out, prepared=True)
    record.update(result)
    record['development_exact_theorem_passed'] = True
except Exception as exc:
    record['development_exact_theorem_passed'] = False
    record['error'] = str(exc)
    traceback.print_exc()
finally:
    for log in sorted(out.glob('*.log')):
        print(f'\n===== {log.name} =====', flush=True)
        print(log.read_text(errors='replace')[-20000:], flush=True)
    (out / 'DEVELOPMENT_STATUS.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2), flush=True)
sys.exit(0 if record.get('development_exact_theorem_passed') else 1)
