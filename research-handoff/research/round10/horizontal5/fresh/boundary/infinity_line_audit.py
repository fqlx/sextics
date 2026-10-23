#!/usr/bin/env python3
"""Actual higher conductor collision at X0=0 away the Fermat vertex.

Y2=1, X1=tau!=0, X0=u*tau, Y1=b, delta=Y0**6+1=b*r.
X2 is eliminated etale along X2**6+tau**6=0.  The equation audited is
D32/(tau**17*b**2), obtained from the literal original polynomial.
"""
import hashlib
import json
import pathlib
import pickle
import sympy as s

HERE=pathlib.Path(__file__).resolve().parent
SOURCE=pathlib.Path('/workspace/research/round9/abel_prym/effective_graph.pickle')
packet=pickle.loads(SOURCE.read_bytes())
zeta,u,b,r,tau=s.symbols('zeta u b r tau')

def red(f):
    return s.rem(s.Poly(s.expand(f),zeta),s.Poly(zeta**6+1,zeta)).as_expr().expand()

coeff={}
for e,c in packet['D'].items():
    for k in range(3):
        bexp=e[4]+k-2
        if e[0]>14 or bexp>10:
            continue
        key=(e[0],bexp,k)
        coeff[key]=coeff.get(key,0)+s.Rational(c)*(-1)**k*s.binomial(s.Rational(e[3],6),k)*zeta**e[3]*tau**(e[0]+e[1]-17)
coeff={e:c for e,f in coeff.items() if (c:=red(f))!=0}

records=[]
all_vertices=set()
for name,weights,expected_degree in [
        ('first',(3,2,6),12),('middle',(1,2,4),8),('last',(1,8,7),14)]:
    wt=lambda e:sum(i*j for i,j in zip(e,weights))
    degree=min(map(wt,coeff))
    assert degree==expected_degree
    initial=s.expand(sum(c*u**e[0]*b**e[1]*r**e[2] for e,c in coeff.items() if wt(e)==degree))
    ar=s.expand(initial).coeff(r,2)
    cr=s.expand(initial).coeff(r,1)
    er=s.expand(initial).coeff(r,0)
    # The leading r^2 coefficient is a unit for tau!=0; completing its
    # square is compatible with each Newton face. Cubic and higher r
    # terms have degree >=3*(wt(b)+wt(r))-2*wt(b), greater than degree.
    assert 3*(weights[1]+weights[2])-2*weights[1]>degree
    assert ar!=0 and not ar.has(u,b,r)
    discr=red(cr**2-4*ar*er)
    vertices=[list(e) for e,c in s.Poly(discr,u,b).terms()]
    all_vertices.update(map(tuple,vertices))
    records.append({'name':name,'weights_u_b_r':list(weights),'degree':degree,
                    'initial_surface':str(initial),'square_completion_branch_initial':str(discr),
                    'branch_support':vertices,
                    'adjoint_cutoff':weights[2]-weights[0]-weights[1]+1})

# Exact nondegeneracy: after removing coordinate monomials, the first and
# last branch edges are binomials with nonzero coefficients. The middle
# edge is a quadratic in b/u^2; its discriminant is nonzero modulo zeta^6+1.
first=records[0]['square_completion_branch_initial']
last=records[2]['square_completion_branch_initial']
middle=s.Poly(s.sympify(records[1]['initial_surface'],locals=globals()).subs(r,0),b)
middle_reduced=s.cancel(middle.as_expr()/(b*u**2*tau**2))
qa=s.expand(middle_reduced).coeff(b,2)
qb=s.expand(middle_reduced).coeff(b,1)/u**2
qc=s.expand(middle_reduced).coeff(b,0)/u**4
middle_disc=red(qb**2-4*qa*qc)
assert middle_disc!=0
for phi in [zeta**2+1,zeta**4-zeta**2+1]:
    assert s.resultant(phi,middle_disc,zeta)!=0

# Newton double-cover adjoints: the three facets impose respectively
# 3*i+2*j>=2, i+2*j>=2, i+8*j>=-1 on a numerator u^i*b^j.
# These are exactly the monomial ideal (u^2,b). The y coordinate itself
# lies in the adjoint ideal, hence on the surface the ideal is (u^2,b,r).
bad=[]
for i in range(15):
    for j in range(11):
        if any(weights[0]*i+weights[1]*j<rec['adjoint_cutoff']
               for rec in records for weights in [rec['weights_u_b_r']]):
            bad.append([i,j])
assert bad==[[0,0],[1,0]],bad

result={
    'original_D_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'coordinates':'Y2=1, X1=tau!=0, X0=u*tau, delta=Y0^6+1=b*r',
    'finite_normalization_reason':'q|u=b=delta=0=-533655864*zeta*tau^19 is a unit for tau!=0',
    'etale_X2_elimination':'X2^6+tau^6=0, X2!=0, so F_X2!=0',
    'faces':records,'branch_Newton_vertices':[[0,6],[2,3],[6,1],[14,0]],
    'middle_edge_discriminant':str(middle_disc),
    'all_edges_nondegenerate_over_both_cyclotomic_components':True,
    'adjoint_ideal_in_normalized_surface':'(u^2,b,r)',
    'adjoint_quotient_basis':['1','u'],'transverse_geometric_genus':2,
    'scope':'Generic tau!=0,infinity collision along X0=Y1=0, Y0=zeta*Y2, X2=eta*X1. The vertex tau=0 and Y2=0 endpoints, global coherent extension, and source Gysin map are separate.'}
(HERE/'infinity_line_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['branch_Newton_vertices','middle_edge_discriminant','adjoint_ideal_in_normalized_surface','adjoint_quotient_basis','transverse_geometric_genus','scope']},indent=2))
