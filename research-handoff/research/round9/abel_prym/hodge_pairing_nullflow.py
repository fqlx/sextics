"""Exact normalization of the open extension against its dual holomorphic form."""
from pathlib import Path
import pickle,sympy as s,json,time
HERE=Path(__file__).parent;start=time.monotonic()
p=pickle.load(open(HERE/'polarization_clean_frame.pickle','rb'));q=pickle.load(open(HERE.parent/'cyclic_full'/'conjugate_fast.pickle','rb'))
W,h,T,L,r,x=q['symbols'];c=s.Rational(5,7);ss,ds=s.symbols('ss ds');C=q['curve'];Ct=s.diff(C,T);CW=s.diff(C,W)
flow=[x*((c*c-10*r)*L+4*r*r),x*r*(c*c-5*r)-18*L+9*r,-x*((c*c+5*r)*x+27)]
assert s.cancel(p['pairing_actual_rows_conjugate_columns'][2,0]-7*x/18)==0
# Contract raw Q8 coefficient by coefficient, retaining exact rational functions.
uflow=0
for k,(component,ex)in enumerate(q['lab8']):
 if component not in(0,1):continue
 coeff=s.cancel(sum(flow[j]*q['primitives'][z][0]['Q8_raw'][k]/q['primitives'][z][0]['Q8_denominator']for j,z in enumerate(('L','r','x'))))
 uflow+=(-1 if component==1 else 1)*coeff*W**(ex[0]+int(component==1))*T**ex[2]
uflow=s.factor(uflow)
Cd=sum(v*s.diff(C,z)for v,z in zip(flow,(L,r,x)))
alpha=(-W*(Cd+Ct*ds)/CW+uflow)/Ct
alpha=alpha.subs({h:1,T:ss})
Lmark=-W**6-c*(1+ss)*W**3-r*ss-ss**3/x
alpha=s.factor(s.cancel(alpha.subs(L,Lmark)))
A=c*(1+ss);K=r*(5*ss+4)+3*ss*(2*ss+3)/x
expected=-(ds+x*K+c*x*W**3)/(3*W*(2*W**3+A))
assert s.cancel(alpha-expected)==0
# The boundary-row eta contraction is supplied independently by off's compact
# formula; verify it against the literal exact boundary packet here.
b=pickle.load(open(HERE.parent/'open_curve'/'boundary_native.pickle','rb'));sp=s.Symbol('s')
def expr(payload):
 def poly(dd):return sum(s.Rational(cc)*L**e[0]*r**e[1]*x**e[2]*sp**e[3]for e,cc in dd.items())
 return poly(payload['numerator'])/poly(payload['denominator'])
E=[s.cancel(sum(flow[j]*expr(b['connection_boundary'][name][i][2])for j,name in enumerate(('L','r','x')))+ds*expr(b['connection_boundary']['s'][i][2]))for i in range(2)]
E=[z.subs(sp,ss)for z in E]
contraction=s.cancel(W**2*((-A-W**3)*E[0]-E[1]))
contraction=s.cancel(contraction.subs(L,Lmark))
assert s.cancel(contraction*7*x/18+alpha/6)==0
out={'exact_QQ_identity':True,'clean_pairing_eta_conjugate_hol':'7*x/18','nullflow_marked_absolute_conjugate_form':str(expected),'nullflow_uflow':str(uflow),'graph_motion_derivative':'ds is arbitrary; may be replaced by delta(T_effective) only after this identity.','theta_extension_pairing':'<nabla(theta_actual)_proper,conjugate_hol> = -(1-zeta^2)/6 * alpha_conjugate(P), along the Prym-nullflow plus arbitrary graph motion.','normalization_scope':'Theta_actual projection carries factor1-zeta². The marked divisor P-sigmaP has conjugate alpha difference (1-zeta²)*alpha(P). Thus our chosen Jacobian residue pairing equals -1/6 times that corrected Abel-Prym derivative.','scope':'Exact leading-Hodge/source normalization along the isoperiodic flow, including all Q8 absolute corrections and moving-graph derivative. Does not solve the closed gamma/source wedge equations or prove a global support H20 class.','seconds':time.monotonic()-start}
(HERE/'hodge_pairing_nullflow.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
