"""Literal K3/double-plane source bridge; no fixed-Jacobian identification.

Only exact rational identities are used.  The entire physical first normal is
transported, including the moving w -> a coordinate cochain.
"""
from pathlib import Path
import json
import sympy as S

A,D,k,R,s,a,h,alpha,w,delta=S.symbols('A D k R s a h alpha w delta')
V=A*k**3+k**2/2
q1=(3*A*k*k+k)*s+k/3
q2=(3*A*k+S.Rational(1,2))*s*s+s/3+D*k
q3=A*s**3+D*s
Q=q2*q2-4*q1*q3
P=S.expand(q3+q2*a+q1*a*a)
Pdelta=(s+k*a)**2
Pa=S.diff(P,a)
checks={}
def check(name,value,relation=None):
    n=S.fraction(S.cancel(value))[0]
    if relation is not None:
        n=S.rem(n,relation,h)
    checks[name]=S.expand(n)==0
    assert checks[name], (name,S.factor(n))

check('normline_is_literal_a0_member',P.subs(a,0)-q3)
check('double_plane_exact_discriminant',
      (2*alpha-P)**2-(P*P-4*R)-4*(alpha*alpha-P*alpha+R))

# Rational forward/inverse coordinates, with the curve equation as the sole
# incidence relation. X=4q1*alpha,Y=X*(q2+2q1*a).
X=4*q1*alpha
Y=X*Pa
E=Y*Y-X**3-Q*X*X-16*R*q1*q1*X
check('EXACT_K3_equation_factor',
      E+64*q1**3*alpha*(alpha*alpha-P*alpha+R))
check('inverse_a_coordinate',(Y/X-q2)/(2*q1)-a)
check('inverse_alpha_coordinate',X/(4*q1)-alpha)
check('rational_curve_Pa',Pa-(q2+2*q1*a))

# d_alpha/alpha=dP/h. Thus at fixed s, dX/Y=da/h. The omitted
# s,R,U legs are retained before wedging dU dR ds, where they vanish.
alpha_a=alpha*Pa/h
check('FULL_holomorphic_density',S.diff(X,alpha)*alpha_a/Y-1/h)

q1d=q1+delta*k*k
q2d=q2+delta*2*k*s
q3d=q3+delta*s*s
Pd=S.expand(q3d+q2d*a+q1d*a*a)
check('FULL_square_missing_normal',S.diff(Pd,delta)-Pdelta)
check('no_dropped_quadratic_delta',S.diff(Pd,delta,2))
check('Qdelta_exact',
      S.diff(q2d*q2d-4*q1d*q3d,delta).subs(delta,0)+4*(V/k)*s**3)
check('Qdelta2_exact',S.diff(q2d*q2d-4*q1d*q3d,delta,2))

m=S.symbols('m')
Pm=A*m**3-V*a**3+a*m*m/2+(D+a/3)*m
check('section_mark_eliminates_a3',P.subs(s,m-k*a)-Pm)
check('constant_square_normal_in_m',Pdelta.subs(s,m-k*a)-m*m)

# E'-coordinate velocity at fixed a, and at fixed original w. For the latter
# alpha=-w² is delta-independent. These are different, and their difference is
# the physical moving-chart correction.
Xa_delta_over_Y=(k*k/q1+Pdelta/h)/Pa
Xw_delta_over_Y=k*k/(q1*Pa)
normal_cochain=Pdelta/(h*Pa)
check('FULL_moving_X_normal_cochain',Xa_delta_over_Y-Xw_delta_over_Y-normal_cochain)
check('normline_graph_FULL_velocity',
      Xa_delta_over_Y.subs(a,0)-(k*k/(q1*q2)+s*s/(q2*h)))

# Full relative differential, imposing h²=P²-4R only when required.
def da(expr):
    return S.diff(expr,a)+S.diff(expr,h)*P*Pa/h
normal_at_fixed_a=-P*Pdelta/h**3
# d(F ds)=-F_a ds da. This is the exact correction from physical fixed w.
physical_coefficient=normal_at_fixed_a-da(normal_cochain)
simple_physical=2*((V/k)*s**3-k*k*P)/(h*Pa**2)
check('WHOLE_physical_normal_with_Cartan_cochain',
      physical_coefficient-simple_physical)
check('square_normal_low_pole_reduction',
      Pdelta-((3*A*(s+k*a)**2+D+a*(s+k*a)+a/3)-D-a*(s+k*a)-a/3)/(3*A))

# Independent even-quartic source replay, without using the previous derivative.
# W²=-4q1(w4+R)+Qw²; alpha=-w², P=-(w²+R/w²), h=-w²+R/w².
even_delta=-4*(k*k*(w**4+R)+(V/k)*s**3*w*w)
even_pulled=-even_delta/(2*h*w*w*Pa**2)
# Compare after imposing the independently derived P=-(w²+R/w²).
even_difference=even_pulled-2*((V/k)*s**3+k*k*(w*w+R/(w*w)))/(h*Pa**2)
check('independent_even_quartic_source_replay',even_difference)

# The exact physical binding supplies an actual marked point of D, not just an
# unweighted target curve. The cubic j equation and V² relation are both kept.
j,U=S.symbols('j U')
boundV=S.symbols('V')
point_error=(A*j**3+D*j)**2-4*R-R*R/(U*U)
point_error=S.rem(S.together(point_error).as_numer_denom()[0],A*j**3+D*j-boundV,j)
point_error=S.rem(point_error,boundV**2-4*R-R*R/(U*U),boundV)
check('ACTUAL_physical_normline_mark',point_error)

# Concrete nonconstant source replay, entirely rational on the double-plane.
# R=1,U=2/3,k=1 gives the ACTUAL A=2,D=1/9,V=5/2.
# The marked section and V²=4R+R²/U² both hold.
vals={A:S.Integer(2),D:S.Rational(1,9),k:S.Integer(1),s:S.Integer(1),a:S.Integer(1),R:S.Integer(1)}
check('concrete_physical_A_binding',vals[A]-(vals[R]**2+1/vals[R]))
check('concrete_physical_D_binding',vals[D]-S.Rational(2,3)**2/4)
check('concrete_physical_V_binding',V.subs(vals)**2-4*vals[R]-vals[R]**2/S.Rational(2,3)**2)
pv=P.subs(vals)
hv=S.sqrt(pv*pv-4)
num_simple=S.simplify(simple_physical.subs(vals).subs(h,hv))
num_whole=S.simplify(physical_coefficient.subs(vals).subs(h,hv))
check('concrete_complete_source_replay',num_simple-num_whole)
assert num_simple!=0
checks['concrete_retained_source_nonzero']=True

out={
 'status':'ACTUAL_K3_NORMLINE_SQUARE_NORMAL_SOURCE_BRIDGE_PASS; FIXED_JACOBIAN_MAP_OPEN',
 'check_count':len(checks),'checks':checks,
 'K3':'Y²=X³+(q2²−4q1q30)X²+16R q1²X',
 'normline':'D:h²=q30²−4R; it is literally a=0, not assumed to be a serving quotient.',
 'rational_map':'alpha=X/(4q1),a=(Y/X−q2)/(2q1),h=alpha−R/alpha; inverse alpha=(P+h)/2,X=4q1alpha,Y=X(q2+2q1a). Thus h²=P²−4R with P=q30+q2a+q1a².',
 'holomorphic_density':'ds∧dX/Y=ds∧da/h. k_R,k_U and all q1,q2 coefficient base legs vanish only after the actual dU∧dR∧ds wedge.',
 'physical_square_normal':'q1_delta=k²,q2_delta=2ks,q30_delta=s² imply P_delta=(s+ka)² exactly. With m=s+ka, P=A m³−V a³+(a/2)m²+(D+a/3)m and P_delta=m²; V=Ak³+k²/2.',
 'WHOLE_physical_source':'beta_pair=(dU∧dR)/(72R) ∧ {−P(s+ka)² ds∧da/h³ + d[(s+ka)² ds/(h(q2+2q1a))]}. The d is the full exterior derivative; base legs are retained before wedging dU dR. This equals the original fixed-w first-normal source.',
 'normline_graph_velocity':'At a=0, contraction is −[k²/(q1q2)+s²/(q2h)]ds, reproducing the full marked graph normal. The q2 poles and q1 data have not been discarded.',
 'physical_source_coefficient':'2[(V/k)s³−k²P]/[h(q2+2q1a)²] in the ds∧da orientation, before the common dU dR/(72R).',
 'actual_extra_normline_mark':'Under V²=4R+R²/U², each root j of Aj³+Dj=V gives the actual point Qj=(j,R/U) on D. All three are retained as a finite cubic marking, not an unweighted scalar trace.',
 'concrete_replay':{'A':2,'D':'1/9','U':'2/3','V':'5/2','k':1,'s':1,'a':1,'R':1,'P':str(pv),'whole_source_coefficient':str(num_simple)},
 'scope':'Positive literal birational source transport and marked normline inclusion. No fixed-JacD/Kummer map, primitive, Gysin equality, or certificate has been proved. Polynomial square normal alone is not claimed to terminate the source. Frozen publication is unchanged.'
}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual K3/normline square-normal source bridge; fixedJac map OPEN')
