#!/usr/bin/env python3
"""Quartic-agent current serving both original N and parameter j=0 poles."""
import json,hashlib
from pathlib import Path
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
import sympy as s
p=Path(__file__).parent;raw=(p/'actual-N-removed-source-results.json').read_bytes();data=json.loads(raw);C=fmpq_mpoly_ctx.get(('i','j','v'));i,j,v=C.gens();D=fmpq_mpoly(data['common_curve_denominator'],C)
GG=[fmpq_mpoly(z,C) for z in data['GammaV_column_numerators']];JJ=[fmpq_mpoly(z,C) for z in data['Gamma_j_column_numerators']]
H=[];Jv=[];checks={}
for k in range(8):
 h,r=divmod(GG[k]-(5*D if k==7 else 0),v);assert not r;H.append(h)
 z,r=divmod(JJ[k],v);assert not r;Jv.append(z)
 checks['GammaV_remainder_divisible_v_row_'+str(k)]=True;checks['Gammaj_divisible_v_row_'+str(k)]=True
ii,jj,w,T,N,L,M=s.symbols('i j w T N L M');z=T*jj*jj/(ii*ii*w*w)
c=-ii*T/(4*w*jj)+28*T*T*jj/(45*ii*w**3)
cj=s.diff(c,jj);CL=(-ii*T/(4*w)+28*T*T*jj*jj/(45*ii*w**3))*M/L
vv=64*jj*jj*w*N*T*T/(9*ii*ii*L)
d=-ii*T/(20*w*jj*jj)+56*T*T/(135*ii*w**3)-CL/6
cv=-16*jj*N*T**3/(9*ii*L)+s.Rational(1792,405)*jj**3*N*T**4/(ii**3*w*w*L)
dv=-s.Rational(16,45)*N*T**3/(ii*L)+s.Rational(3584,1215)*jj*jj*N*T**4/(ii**3*w*w*L)-vv*CL/6
e=-s.Rational(364,135)*T*T/(ii*w**3)+5*CL/6
checks['current_times_v_no_j_pole']=s.cancel(c*vv-cv)==0
checks['coefficient_d_times_v_no_j_pole']=s.cancel(d*vv-dv)==0
checks['scalar_e_j_poles_cancel']=s.cancel(-5*d-cj-e)==0
checks['c_Lj_over_L_no_j_pole']=s.cancel(c*jj*M/L-CL)==0
# Equality on N=0, which guarantees every original N residue is preserved.
checks['current_matches_N_serving_residue']=s.factor((c-9*ii**3*w/(160*jj**3)).subs(T,s.Rational(9,16)*ii*ii*w*w/(jj*jj)))==0
k=16*c*jj**3/(27*ii**3*w)
checks['exact_N_division_identity']=s.cancel((k-s.Rational(1,30))-(16*z-9)*(56*z+9)/2430)==0
assert all(checks.values()),checks
out=p/'actual-N-j-removed-source-results.json'
res={
 'status':'Explicit actual horizontal current serves all original N and j0 poles; remaining source still open','certificate':False,
 'source_volume':'di dj dw','basis':data['basis'],'current_direction':'fixed-w j current, full Gamma_j+(v_j/(6v))*GammaV retained',
 'current_c':'-i*T/(4*w*j)+28*T²*j/(45*i*w³)','current':'Pj=c*e_bq; Pi=Pw=0; retain all audited rational fiber primitive terms',
 'notation':{'T':'1+w³','N':'9i²w²-16j²T','L':'256T⁵N+729i⁶j²w⁶','v':'64j²wNT²/(9i²L)','M':'L_j/j, a polynomial in i,j,w','CL':'[-iT/(4w)+28T²j²/(45iw³)]*M/L=cL_j/L'},
 'remaining_source':'R=64i*w²*T³/L*Bvector-cv*Jvector-dv*Hvector+e*e_bq',
 'cv':'-16jNT³/(9iL)+1792j³NT⁴/(405i³w²L)',
 'dv':'-16NT³/(45iL)+3584j²NT⁴/(1215i³w²L)-v*CL/6',
 'e':'-364T²/(135iw³)+5CL/6',
 'Bvector_numerators':data['Bvector_numerators'],
 'Hvector_numerators':[str(z) for z in H],
 'Jvector_numerators':[str(z) for z in Jv],
 'common_curve_denominator':str(D),
 'vector_definitions':'B=(Q+GammaV[:,7]/30)/v; H=(GammaV[:,7]-5e_bq)/v; Jvector=Gamma_j[:,7]/v',
 'remaining_denominator_scope':'Only i,w,L,D(v(w)) remain explicitly. Neither N,j nor criticalv_w is a denominator. Intersections of remaining divisors still require full source-serving treatment.',
 'fiber_current_references':data['fiber_primitive_files'],
 'source_parent_sha256':hashlib.sha256(raw).hexdigest(),'checks':checks,
}
out.write_text(json.dumps(res,indent=2)+'\n');print('passed',len(checks),'exact groups; saved',out)
