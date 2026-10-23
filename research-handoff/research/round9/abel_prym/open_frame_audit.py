"""Exact independent residue, third-kind and moving-graph convention audit."""
from pathlib import Path
import pickle,json,time
import sympy as s
HERE=Path(__file__).parent;start=time.monotonic()
u,A,B,da,db=s.symbols('u A B da db');Delta=A*A-4*B
ours=s.Matrix([[(-A*B*da+(10*B-2*A*A)*db)/(3*B*Delta),(4*B*da-2*A*db)/(3*B*Delta)],[(2*B*da-A*db)/(3*Delta),(-2*A*da+4*db)/(3*Delta)]])
parent=pickle.load(open(HERE/'residue_connection.pickle','rb'))
pp=dict(zip(parent['symbols'],(u,A,B,da,db)))
assert all(s.cancel(z)==0 for z in ours-parent['matrix'].subs(pp))
def red(expr):
 num,den=s.fraction(s.cancel(expr));iv=s.invert(den,u*u+A*u+B,u)
 return s.cancel(s.rem(num*iv,u*u+A*u+B,u))
du=red(-(da*u+db)/(2*u+A));um=-A-u;ulog=red(du/u)
g=s.Matrix([um,-1]);dg=s.Matrix([-da-du+s.Rational(2,3)*um*ulog,-s.Rational(2,3)*ulog])
assert all(red(z)==0 for z in dg+ours.T*g)
assert s.cancel(s.trace(ours)+s.Rational(2,3)*db/B+(2*A*da-4*db)/(2*Delta))==0
# Exact polynomial division over the algebraic marked point and cube root.
W,w,zeta=s.symbols('W w zeta');zpoly=zeta*zeta+zeta+1
rr=lambda e:s.rem(s.Poly(s.expand(e),zeta),s.Poly(zpoly,zeta)).as_expr()
Ce=W**6+A*W**3-w**6-A*w**3
qw,rem=s.div(Ce,W-w,W);assert rem==0
qz,rem=s.div(Ce,W-zeta*w,W);assert rr(rem)==0
num=rr(qw-qz)
actual=sum(co*W**ex[0] for ex,co in s.Poly(num,W).terms() if ex[0]%3==0)
expected=(1-zeta*zeta)*w*w*(W**3+w**3+A)
assert rr(actual-expected)==0
assert rr(num.subs(W,w)-s.diff(Ce,W).subs(W,w))==0
assert rr(num.subs(W,zeta*w)+s.diff(Ce,W).subs(W,zeta*w))==0
assert s.degree(num,W)==4
assert not any(ex[0]%3==2 for ex,co in s.Poly(num,W).terms())
# Direct rational moving-curve derivatives, without open-frame reductions.
T,L,r,x,ss,c=s.symbols('T L r x ss c');C=W**6+c*(1+T)*W**3+L+r*T+T**3/x;D=T-ss;Ct=s.diff(C,T)
checks=[]
for j in(0,1):
 P=W**(3*j);f=P/(D*Ct)
 assert s.cancel(s.diff(f,ss)-P/(D*D*Ct))==0
 checks.append([j,'ss'])
 for zz in(L,r,x):
  Cz=s.diff(C,zz);lhs=s.diff(f,zz)-Cz/Ct*s.diff(f,T)
  K=P*Cz/D;rhs=-(s.diff(K,T)*Ct-K*s.diff(Ct,T))/Ct**3
  assert s.cancel(lhs-rhs)==0
  checks.append([j,str(zz)])
result={'all_exact_QQ_checks_pass':True,'parent_residue_block_matches_independent_closed_formula':True,
 'residue_matrix':[[str(z)for z in row]for row in ours.tolist()],
 'residue_basis':'sigma_j=W^(3j)dW/((T-ss)Ct), j=0,1; residues -w^(3j)/CW(w,ss).',
 'infinity_orders':[4,1],
 'infinity_reason':'q=h/W; Waff=q^-1,Taff=tau*q^-2 with tau(0)^3=-x; Ct~3tau^2*q^-4/x and dWaff=-q^-2 dq. Hence sigma0~q^4 dq and sigma1~q dq.',
 'third_kind':'theta=[Ce(W)/(W-w)-Ce(W)/(W-zeta*w)]dT/((T-ss)CW); residues +1,-1 at marked pair, regular elsewhere including infinity.',
 'actual_character_projection':'theta_chi=(1-zeta^2)*w^2*((-A-w^3)*sigma0-sigma1), exactly as rational differentials.',
 'no_invariant_theta_character':True,'marked_coefficient_horizontal':'With u=w^3, other_root=-A-u, f=w^2*(other_root,-1), exact df+R^T*f=0.',
 'proper_derivative_normalization':'If E0,E1 are proper parts of the two boundary rows in the full rank5 connection, nabla(theta_chi)_proper=(1-zeta^2)*w^2*(other_root*E0-E1). No derivative-of-coefficient proper term appears.',
 'moving_graph_checks':checks,
 'pullback_rule':'After ss=e=N1/N0(L,r,x,z), pull back K_L dL+K_r dr+K_x dx+K_ss de; de includes derivative in the source z, which itself depends on all physical a,b,v.',
 'scope':'Exact normalization audit of the open-curve extension and its marked third-kind representative. It does not compute the proper extension rows, solve closed gamma, match source, or provide a certificate.',
 'seconds':time.monotonic()-start}
(HERE/'open_frame_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
