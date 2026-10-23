#!/usr/bin/env python3
"""Exact coordinate, character and generic-adjoint-jet audit at the D32 corner.

This does not identify the extension across v=infinity or solve the global
adjoint restriction map.  Those require the further boundary resolution.
"""
from pathlib import Path
import hashlib
import json
import pickle
import sympy as s
import yaml

HERE = Path(__file__).resolve().parent
REC = Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec')
GRAPH = Path('/workspace/research/round9/abel_prym/effective_graph.pickle')
record = yaml.safe_load(REC.read_text())
graph = pickle.loads(GRAPH.read_bytes())['D']
X = s.symbols('X0 X1 X2 Y0 Y1 Y2')
ep, vv, ww, aa, bb, rr = s.symbols('eps v W a b r')
def original(name):
    return sum(s.Rational(c)*s.prod(x**n for x,n in zip(X, ex))
               for c,ex in record['polynomialData'][name]['terms'])
F, target = original('F'), original('A')
sub = dict(zip(X, (ep, vv*ep, ww, aa, bb, 1)))
Ft, At = s.expand(F.subs(sub)), s.expand(target.subs(sub))
c = s.Rational(5,7)
expected = (ww**6+aa**6+bb**6+1
            + c*bb*(1+aa*vv)*ww**3*ep
            + c*(aa*bb+vv*bb**3)*ep**2+c*ww**3*ep**3
            + c*aa*bb*vv*ep**4+(1+vv**6)*ep**6)
assert s.expand(Ft-expected)==0 and At==ep**3*aa**3

# The coordinates after the two blowups are (eps,W,b,r,v), with
# a^6+1=b*r.  For computing the Jacobian only, impose da/dr=b/(6a^5)
# and da/db=r/(6a^5).  The standard projective Omega has minus sign on Y2=1.
J=s.Matrix([[1,0,0,0,0],
            [vv,0,0,0,ep],
            [0,1,0,0,0],
            [0,0,rr/(6*aa**5),bb/(6*aa**5),0],
            [0,0,1,0,0]])
jac=s.factor(J.det())
assert jac==ep*bb/(6*aa**5)
source=s.cancel(-At*jac)
assert source==-ep**4*bb/(6*aa**2)
uu=s.symbols('u')
Jinf=s.Matrix([[uu,0,0,0,ep],
              [1,0,0,0,0],
              [0,1,0,0,0],
              [0,0,rr/(6*aa**5),bb/(6*aa**5),0],
              [0,0,1,0,0]])
source_inf=s.cancel(-(uu*ep)**3*aa**3*Jinf.det())
assert source_inf==uu**3*ep**4*bb/(6*aa**2)

# Verify the graph's first exceptional multiplicity and both involutions
# directly against every original monomial, without a Taylor intermediary.
radial_orders=sorted({e[0]+e[1] for e in graph})
assert radial_orders==[17,19]
assert all(e[2]==0 and sum(e)==32 for e in graph)
assert all((e[3]+e[4]+e[5])%2==1 for e in graph)
assert all((e[0]+e[1]+e[2])%2==1 for e in graph)
delta_weights=(0,4,0,1,1,5)
assert {sum(i*j for i,j in zip(e,delta_weights))%6 for e in graph}=={5}

# At the generic conductor corner the graph is D=eps^17*b^2*D2.
# Its b^2 divisibility and weighted initial form are independently audited
# by fresh/boundary/weighted_ci_audit.py.  Therefore the displayed exact
# Jacobian makes the coefficient of the local CI canonical frame below.
canonical_coefficient=s.cancel(jac/(ep**17*bb**2))
assert canonical_coefficient==1/(6*aa**5*ep**16*bb)

# Universal homogeneous polynomial families realizing the six low jets.
delta=aa**6+1
families=[
    dict(jet='1',     xorder=16, Y1=1, delta=0, W=0, Pdegree=15),
    dict(jet='eps',   xorder=17, Y1=1, delta=0, W=0, Pdegree=14),
    dict(jet='eps^2', xorder=18, Y1=1, delta=0, W=0, Pdegree=13),
    dict(jet='b',     xorder=16, Y1=2, delta=0, W=0, Pdegree=14),
    dict(jet='r',     xorder=16, Y1=0, delta=1, W=0, Pdegree=10),
    dict(jet='W^3',   xorder=16, Y1=1, delta=0, W=3, Pdegree=12),
]
for row in families:
    total=row['xorder']+row['Y1']+6*row['delta']+row['W']+row['Pdegree']
    assert total==32
    g=ep**row['xorder']*bb**row['Y1']*delta**row['delta']*ww**row['W']
    # Strip off the common canonical unit 1/(6a^5); this is constant
    # through weight7 since a=zeta*(1-br)^(1/6), wt(br)=12.
    got=s.cancel((g/(ep**16*bb)).subs(aa**6,bb*rr-1))
    want={'1':1,'eps':ep,'eps^2':ep**2,'b':bb,'r':rr,'W^3':ww**3}[row['jet']]
    assert s.expand(got-want)==0
    row['v_polynomial_degree_bound']=row['xorder']
    row['generic_total_canonical_jet_line_degree']=16+{'eps':1,'eps^2':2}.get(row['jet'],0)
    row['Y_sign']=(-1)**(32-row['xorder']-row['W'])
    row['Y_normal_order']=32-row['xorder']-row['W']
    row['six_zeta_values_interpolate']=row['Pdegree']>=5
    # The fine diagonal delta has weights (0,4,0,1,1,5) in the
    # original coordinates.  Omega/D is delta invariant, so g must
    # have the actual source character2.  Delta=a^6+1 is invariant.
    fine_pairs=[]
    for k in range(row['xorder']+1):
        for j in range(6):
            if (4*k+row['Y1']+5*row['Pdegree']-4*j)%6==2:
                fine_pairs.append((k,j))
    row['source_delta2_polynomial_count']=len(fine_pairs)
    row['source_delta2_k_minus_j_mod3']=sorted({(k-j)%3 for k,j in fine_pairs})

# Over Q[zeta]/(zeta^6+1), the common canonical unit is
# 1/(6*zeta^5)=-zeta/6.  Thus Y0^j*Y2^(Pdegree-j), 0<=j<=5,
# gives an exact basis of the simultaneous six-corner coefficient algebra.
zz=s.symbols('zeta')
cols=[]
for j in range(6):
    rem=s.rem(s.Poly(-zz**(j+1)/6,zz),s.Poly(zz**6+1,zz))
    cols.append([rem.coeff_monomial(zz**i) for i in range(6)])
corner_matrix=s.Matrix(6,6,lambda i,j:cols[j][i])
assert corner_matrix.rank()==6
all_generic_jet_columns=sum(6*(row['v_polynomial_degree_bound']+1) for row in families)
even_generic_jet_columns=sum(6*(row['v_polynomial_degree_bound']+1)
                             for row in families if row['Y_sign']==1)
assert (all_generic_jet_columns,even_generic_jet_columns)==(630,420)
fine_generic_jet_columns=sum(row['source_delta2_polynomial_count']
                             for row in families if row['Y_sign']==1)
assert fine_generic_jet_columns==140

# Under eps'=v*eps, v'=1/v, W,b,r fixed, the four transverse
# coordinate volume scales by v and dv'=-v^-2 dv.  D2'=v^-17 D2.
relative_factor=vv/(vv**(-17))
total_factor=-relative_factor/vv**2
assert relative_factor==vv**18 and total_factor==-vv**16

out={
 'instance_sha256':hashlib.sha256(REC.read_bytes()).hexdigest(),
 'graph_sha256':hashlib.sha256(GRAPH.read_bytes()).hexdigest(),
 'coordinates':'Y2=1; X0=eps,X1=v*eps,X2=W,Y0=a,Y1=b; a^6+1=b*r',
 'orientation':'Omega=sum(-1)^i Zi dZ_except_i; ordered new volume deps,dW,db,dr,dv',
 'literal_F_and_target_verified':True,
 'ambient_chart_jacobian':str(jac),
 'actual_source_numerator_over_F_squared':str(source),
 'infinity_chart_source_numerator_over_F_squared':str(source_inf),
 'source_weighted_numerator_degree':18,
 'weights_eps_W_b_r':[3,2,6,6],
 'source_ambient_radial_exponent_after_F_squared':10,
 'graph_radial_orders':radial_orders,
 'strict_graph_b_squared_input':'independent weighted_ci_audit.py verifies at the corner',
 'global_canonical_g_local_coefficient':'g/(6*a^5*eps^16*b)',
 'generic_v_transition':{'eps_prime':'v*eps','v_prime':'1/v',
      'F_prime':'F','D2_prime':'v^-17*D2',
      'relative_canonical_frame_prime':'v^18*Omega_relative',
      'total_canonical_frame_prime':'-v^16*Omega_total'},
 'mu3':'W->zeta3*W: local CI canonical frame has character zeta3; six listed coefficients have character1',
 'Y_sign':'eps,W->-eps,-W; a,b,r,v fixed. Local CI canonical frame is invariant.',
 'relevant_Y_even_chi1_adjoint_jets':['1','eps^2','b','r'],
 'other_chi1_adjoint_jets_Y_odd':['eps','W^3'],
 'six_global_polynomial_families':families,
 'simultaneous_corner_coefficient_rank':6,
 'simultaneous_corner_coefficient_determinant':str(corner_matrix.det()),
 'generic_full_jet_section_rank':all_generic_jet_columns,
 'generic_Y_even_chi1_jet_section_rank':even_generic_jet_columns,
 'generic_full_source_fine_character_jet_section_rank':fine_generic_jet_columns,
 'source_fine_diagonal':{'original_weights_mod6':delta_weights,
     'target_A_character':3,'Omega_character':5,'source_character':2,
     'D32_character':5,'global_canonical_Omega_over_FD_character':0,
     'required_global_g_character':2,
     'corner_chart_action':'eps->omega*eps,W->omega*W,a,b->omega²*(a,b),r->omega4*r,v->omega4*v; omega6=1',
     'local_CI_total_canonical_character':2},
 'generic_jet_section_rank_scope':'The displayed polynomial subspace surjects onto the generic O(16+i) direct-sum jet model. This is conditional on that model at special v and on other global adjoint conditions; neither is asserted.',
 'all_families_normal_X_order_at_least':16,
 'all_families_Y_order_at_least':min(row['Y_normal_order'] for row in families),
 'scope':['Exact pinned source density, coordinate Jacobian and character matching.',
          'Exact generic v-overlap transition and polynomial jet-family matching.',
          'No assertion of bundle extension through v infinity or other special v.',
          'No assertion that these polynomials satisfy every other adjoint condition.',
          'Source character matching is not a computation of its global Gysin preimage.']}
(HERE/'source_transition.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
