import sympy as s, json
from pathlib import Path
root=Path(__file__).parent
raw=json.loads((root/'reconstructed-connection.json').read_text())
p,H,C=s.symbols('p H C')
loc={'p':p,'H':H,'C':C}
f=(H+C*p)**2-4*p**6
bs=raw['basis']; mats={}; checks=[]
for v in (H,C):
    cols=[[s.sympify(a,locals=loc)for a in col]for col in raw[str(v)]['columns']]
    mats[v]=s.Matrix.hstack(*(s.Matrix(col)for col in cols))
    for j,rs,col in zip(bs,raw[str(v)]['primitives'],cols):
        R=sum(s.sympify(r,locals=loc)*p**i for i,r in enumerate(rs))
        E=-p**j*s.diff(f,v)/2-sum(a*p**i*f for i,a in zip(bs,col))-s.diff(R,p)*f+R*s.diff(f,p)/2
        assert s.cancel(E)==0
        checks.append(f'Dwork-{v}-{j}')
MH,MC=mats[H],mats[C]
assert (6*H*MH+4*C*MC-s.diag(*(2*j-4 for j in bs))).applyfunc(s.cancel)==s.zeros(4)
checks.append('Euler')
# ∇H∇C−∇C∇H=0 on coefficient columns.
flat=MC.diff(H)-MH.diff(C)+MH*MC-MC*MH
assert flat.applyfunc(s.cancel)==s.zeros(4)
checks.append('flatness')
L=4*H*(4*C**6-729*H**4)
polys={v:(L*mats[v]).applyfunc(s.cancel)for v in (H,C)}
for mat in polys.values():
    for a in mat: assert s.denom(a)==1
out={'basis':bs,'common_denominator':str(L),'H_numerator_rows':[[str(a)for a in polys[H].row(i)]for i in range(4)],'C_numerator_rows':[[str(a)for a in polys[C].row(i)]for i in range(4)],'checks':checks}
(root/'connection-audit.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
