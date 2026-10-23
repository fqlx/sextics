#!/usr/bin/env python3
"""Independent line/character/Koszul calculation for the physical cone model.

This is a global arithmetic calculation for the full unsaturated pencil CI;
it does not compute boundary conductor or normalization corrections.
"""
import json,math
from pathlib import Path
HERE=Path(__file__).resolve().parent
def add(*a):return tuple(sum(t) for t in zip(*a))
def mul(k,a):return tuple(k*t for t in a)
def sub(a,b):return add(a,mul(-1,b))
def cohomology(a):
    m,n=a;p2=[0,0,0];p1=[0,0]
    if m>=0:p2[0]=(m+1)*(m+2)//2
    if m<=-3:p2[2]=(-m-1)*(-m-2)//2
    if n>=0:p1[0]=n+1
    if n<=-2:p1[1]=-n-1
    return [sum(p2[i]*p1[j] for i in range(3) for j in range(2) if i+j==k) for k in range(4)]
KB=(-3,-2);M=(15,17);F=(0,1);T=(-2,2);N=add(M,T)
rw=add(M,F);zw=add(M,mul(2,F));Q=add(mul(2,M),mul(2,F));G=add(mul(3,M),mul(6,F))
K=add(KB,mul(-1,rw),mul(-1,zw),Q,G)
assert K==add(KB,mul(3,M),mul(5,F))==(42,54)
module=[(0,0),zw,mul(2,zw),rw,add(rw,zw),add(rw,mul(2,zw))]
chars=[0,2,1,1,0,2]
H2=sum(cohomology(mul(-1,w))[2] for w in module);assert H2==0
KZ=add(KB,M,N);assert KZ==(25,34)
jets=[K,sub(K,M),sub(K,N)]
E=[sub(KZ,L) for L in jets]
assert E==[(-17,-20),(-2,-3),(-4,-1)]
generators=[sub(K,mul(2,M)),sub(K,add(M,N)),sub(K,mul(2,N))]
syzygies=[sub(K,add(mul(2,M),N)),sub(K,add(M,mul(2,N)))]
assert generators==[(12,20),(14,18),(16,16)] and syzygies==[(-1,1),(1,-1)]
assert all(not any(cohomology(L)) for L in syzygies)
assert all(not any(cohomology(L)[1:]) for L in generators)
h0J2=sum(cohomology(L)[0] for L in generators)
h0K=cohomology(K)[0];target=h0K-h0J2
canonical_slots=[sub(K,w) for w,ch in zip(module,chars) if (1+ch)%3==1]
assert canonical_slots==[(42,54),(12,17)]
canonical_dim=sum(cohomology(L)[0] for L in canonical_slots)
def z_h0(L):return cohomology(L)[0]-cohomology(sub(L,M))[0]-cohomology(sub(L,N))[0]+cohomology(sub(L,add(M,N)))[0]
graded_h0=[z_h0(L) for L in jets]
assert sum(graded_h0)==target
deg=lambda a:a[0]*(M[0]*N[1]+M[1]*N[0])+a[1]*M[0]*N[0]
arith_genus=1+deg(KZ)//2
out={'base':'P2_Y x P1_X','line_bidegrees':{'KB':KB,'d':M,'n':N,'w_old':F,'t_old_over_h2':T,'r=d*w':rw,'z=d*w²':zw,'quadric':Q,'cubic':G,'omegaY':K,'omegaZ_full_CI':KZ},
 'finite_module_basis':['1','z','z²','r','rz','rz²'],'finite_module_characters':chars,'omegaY_character':1,'H2_OY':H2,
 'target_character':'R1 chi² / canonical chi¹','R1_graded_lines_constant_then_linear':E,'dual_adjoint_graded_lines':jets,
 'non_split_warning':'R1 is an I²-annihilated module; I acts from the rank2 n0 layer to n1 line. These are graded lines, not a direct-sum identification.',
 'square_ideal_generators_after_omega_twist':generators,'square_ideal_syzygies_after_omega_twist':syzygies,'syzygy_cohomology':[cohomology(L) for L in syzygies],
 'H1_square_ideal_omega_twist':0,'canonical_chi1_slots':canonical_slots,'canonical_chi1_dimension':canonical_dim,
 'full_CI_arithmetic_genus':arith_genus,'full_CI_not_normalization_genus':True,'adjoint_cone_chi1_jet_space_dimension':target,'graded_jet_space_dimensions':graded_h0,
 'cone_jet_map_surjective_from_constant_canonical_slot':True,'kernel_chi1_canonical_dimension_if_only_cone_conditions':canonical_dim-target,
 'scope':'Exact finite-flat physical model and full-pencil Koszul jet interpolation. Does not impose normalization/conductor/other-boundary adjoint conditions. Does not prove physicalD32 H20=0 or serving.'}
(HERE/'global_cone_twists.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
