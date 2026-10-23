"""Full fixed-denominator certificate construction on the new factor support.

This is one geometrically motivated denominator, not a degree-bounded claim.
The exact target and sparse arithmetic are imported from the original packet.
"""
import sys, json, time
from pathlib import Path

sys.path.insert(0, '/workspace/off-paired-research-published')
from ansatz import F, A, Q, mul, system, rankmod, rankexact, char

ROOT = Path(__file__).resolve().parent
D3 = {(0,2,0,0,1,0): Q(3), (2,0,0,1,0,0): Q(2)}
D4 = {(0,2,1,0,0,1): Q(1), (3,0,0,1,0,0): Q(1)}
D = mul(D3,D4)

def run_case(label, denominator):
    start = time.time()
    cols, rhs, rows, names = system(denominator)
    report = {
      'label': label,
      'scope': 'one geometrically motivated fixed denominator; no unrestricted exclusion',
      'D': [[list(e),str(c)] for e,c in denominator.items()],
      'degree': sum(next(iter(denominator))),
      'character': list(char(next(iter(denominator)))),
      'rows': len(rows), 'columns': len(cols),
    }
    p = 1000003
    r, _ = rankmod(cols,rows,p)
    ra, _ = rankmod(cols+[rhs],rows,p)
    report['modular'] = {'prime':p, 'rank':r,'augmented_rank':ra}
    re, _ = rankexact(cols)
    rea, _ = rankexact(cols+[rhs])
    report['exact'] = {'rank':re,'augmented_rank':rea}
    report['status'] = 'no_solution_for_this_fixed_D' if rea>re else 'consistent_needs_solution_extraction'
    report['seconds'] = time.time()-start
    print(json.dumps(report),flush=True)
    return report


if __name__ == '__main__':
    report = {
      'scope': 'two specific factor-support constructions, no denominator-power sweep',
      'target': {'q': 1, 'F': [[list(e),str(c)] for e,c in F.items()],
                 'A': [[list(e),str(c)] for e,c in A.items()]},
      'D3': [[list(e),str(c)] for e,c in D3.items()],
      'D4': [[list(e),str(c)] for e,c in D4.items()],
      'cases': [run_case('D3*D4', D), run_case('D4^2', mul(D4,D4))],
    }
    (ROOT/'factor-support-certificate-results.json').write_text(json.dumps(report,indent=2)+'\n')
