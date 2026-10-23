"""Rational selected-sheet canonical data on the new CM-E1 graph.

No Gysin matching or target current follows just from this section.
"""
import json
from pathlib import Path
import sympy as S

Q=S.symbols('Q',nonzero=True)
kappa=(Q-16)**3/(16*Q**2)
V=2*(Q-16)/(3*(Q+32))
W=-16*Q*(Q-16)/(Q+32)**3
theta=lambda expression:S.cancel(kappa*S.diff(expression,Q)/S.diff(kappa,Q))
checks=[]
def check(name,expression):
    assert S.cancel(expression)==0,(name,S.factor(expression))
    checks.append(name)
check('canonical-V-connection',theta(V)+2*W)
check('canonical-W-connection',theta(W)-(3*V+(27-2*kappa)*W)/(4*kappa+27))
check('canonical-F-value',V+S.Rational(1,3)-Q/(Q+32))
X=S.symbols('X',nonzero=True)
b=(X**3-64)/(4*X**2)
F=X**3/(X**3+128)
R0=-64*X**3*(X**3-64)/(X**3+128)**3
check('normalized-S3-kappa',kappa.subs(Q,X**3/4)-b**3)
check('normalized-S3-V',V.subs(Q,X**3/4)-(F-S.Rational(1,3)))
check('normalized-S3-W',W.subs(Q,X**3/4)-R0)
M,N,B,H,C=S.symbols('M N B H C',nonzero=True)
check('graph-clearing',16*N*M**4*(B**3-H**2*C*kappa.subs(Q,M**2/N))-(16*N*M**4*B**3-H**2*C*(M**2-16*N)**3))
data={
 'status':'Exact full two-component selected-sheet section; no target Gysin matching or primitive',
 'checks':checks,'check_count':len(checks),
 'Q':'(u^6+v^6)^2/(u^6*v^6)',
 'kappa':str(kappa),'V':str(V),'W':str(W),
 'graph':'16*N*M^4*B^3-H^2*C*(M^2-16*N)^3=0, M=u^6+v^6,N=u^6*v^6',
 'warning':'The rational section is necessary residue data on one graph sheet; its Gysin image has not been matched to the actual source',
}
Path(__file__).with_name('k3-graph-section-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact graph-section identities')
