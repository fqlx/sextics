#!/usr/bin/env python3
"""Remove the actual w=0 scalar integration constant, retaining curve defect."""
import hashlib,json
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent
i,u,w=s.symbols('i u w')
data_path=HERE.parent/'ruling-source/adjoint-reconstruction/n-only-hermite-results.json'
data=json.loads(data_path.read_text())
assert data['all_three_full_derivative_identities']
binding=json.loads((HERE/'corrected-rational-source-binding.json').read_text())
assert data['source_sha256']==binding['source_sha256']
constants={}
for label,part in data['components'].items():
    c=s.sympify(part['polynomial_primitive_coefficients'][0],locals={'u':u})
    for term in part['proper_primitive_terms']:
        c+=s.sympify(term['numerator_coefficients'][0],locals={'u':u})/(-16*u)**term['denominator_power']
    constants[label]=s.factor(c)
assert constants['i^-7']==0

T=1+w**3;N0=9*w**2-16*u*T
L=256*i**2*T**5*N0+729*i**8*u*w**6
v=64*i**2*u*w*N0*T**2/(9*L)
vi=s.diff(v,i)-2*u/i*s.diff(v,u)  # physical partial_i at fixed J,w
vJ=s.diff(v,u)/i**2               # physical partial_J at fixed i,w
vw=s.diff(v,w)
def lead(f):
    p,q=s.fraction(s.cancel(f))
    pp=s.Poly(p,w);qq=s.Poly(q,w)
    op=min(k[0] for k,c in pp.terms() if c)
    oq=min(k[0] for k,c in qq.terms() if c)
    return op-oq,s.factor(pp.coeff_monomial(w**op)/qq.coeff_monomial(w**oq))
leading={
    'v':lead(v),
    'vi_over_vw':lead(vi/vw),
    'vJ_over_vw':lead(vJ/vw),
    'v_over_vw':lead(v/vw),
    'D_w':lead((6*v+2*i*vi+2*i**2*u*vJ)/vw),
}
assert leading['v']==(1,u/36)
assert leading['vi_over_vw']==(1,-2/i)
assert leading['vJ_over_vw']==(1,1/(i**2*u))
assert leading['v_over_vw']==(1,s.Integer(1))
assert leading['D_w']==(1,s.Integer(4))

# Valuation proof: A,B,Z,D preserve w^m O(1). EA,EB,EZ,ED
# lower that order by at most one, since v has a simple zero and
# vi,vJ have order one. Parameter derivatives at fixed w preserve order.
# h,F,G have order>=3; t has order>=1 and v*t order>=2.
# Thus source/PE/PD corrections have order>=2; EA3(vt)>=1,
# and W(t)/v=v*(...)(...)t has order>=2. Hence Ctot>=1.
valuation_bounds={
    'h':3,'F':3,'G':3,'t':1,'v*t':2,
    'ES(h)':2,'EPE(F)':2,'EPD(G)':2,'EA3(v*t)':1,'W(t)/v':2,
    'Ctot':1,
}
c1=constants['i^-1'];c2=constants['i^-2']
out={
    'source_sha256':binding['source_sha256'],
    'n_only_hermite_sha256':hashlib.sha256(data_path.read_bytes()).hexdigest(),
    'coordinates':'u=J/i^2; all i,J partials in statements hold w fixed unless marked A,B',
    'PN_at_w0':{'i^-1':str(c1),'i^-2':str(c2),'i^-7':'0'},
    'leading_terms':{key:{'w_order':order,'coefficient':str(c)} for key,(order,c) in leading.items()},
    'valuation_lower_bounds':valuation_bounds,
    'integration_freedom':'K -> K+v*C(i,J), since (Z-1)(v*C)=0',
    'selected_C':'C=-i^-1*c1(u)-i^-2*c2(u)',
    'normalized_K':'Kreg=K-v*(i^-1*c1(u)+i^-2*c2(u))',
    'exact_orders':'Kreg/v=O(w), Kreg=O(w^2), (D-7)Kreg=O(w^2)',
    'curve_defect_shift':'(D-7)(v*C)=v*(D-1)C, with D C=-2i*C_i-2J*C_J',
    'normalized_defect_shift':'-v*[i^-1*(2theta+1)c1+i^-2*(2theta+3)c2], theta=u*partial_u',
    'cover_regularity':'On e^6=v~u*w/36, e^-7*Kreg=O(e^5) and e^-8*(D-7)Kreg=O(e^4)',
    'scope':'Source-specific normalization only; all compact and infinity defect rows retained',
    'checks':7,'certificate':False,
}
(HERE/'actual-rational-k-normalization.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':7,'normalized_K_order':2,'cover_orders':[5,4],'certificate':False},indent=2))
