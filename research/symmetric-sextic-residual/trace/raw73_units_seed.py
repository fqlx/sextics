"""Replay raw73 DAG at its F37 seed, including every recorded source-unit node."""
import json
from hashlib import sha256
from pathlib import Path
from flint import nmod_mat

path = Path(__file__).resolve().parent / 'raw73-outer-source-circuit.json'
packet = json.loads(path.read_text())
assert packet['input_sha256'] == '1c2d046748b5536685ce2abe4e5a45395cd84f1d1d5fa6bd56e2bc17cd31bb21'
p = 37
vals = []
for op, a, b in packet['nodes']:
    if op == 'const': v = a * pow(b, -1, p)
    elif op == 'input': v = packet['seed_inputs'][a]
    elif op == 'add': v = vals[a] + vals[b]
    elif op == 'mul': v = vals[a] * vals[b]
    elif op == 'neg': v = -vals[a]
    elif op == 'inv': v = pow(vals[a], -1, p)
    elif op == 'det':
        assert len(b) == a * a
        v = int(nmod_mat([[vals[b[i*a+j]] for j in range(a)] for i in range(a)], p).det())
    else: raise ValueError(op)
    vals.append(v % p)

unit_values = [vals[i] for i in packet['source_unit_nodes']]
J = vals[packet['full_incidence_jacobian_node']]
assert all(unit_values) and J == packet['seed_check']['J73'] == 10
assert all(vals[i] == 0 for i in packet['equations'])
print('packet sha256', sha256(path.read_bytes()).hexdigest())
print('73 equations zero, J73', J, 'source units', unit_values)
