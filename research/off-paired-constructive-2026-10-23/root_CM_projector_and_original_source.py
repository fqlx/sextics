"""Independent actual CM projector and full off-paired source-density binding.
No claim that endpoint correction terms have been cancelled.
"""
from pathlib import Path
import sympy as s,json
x1,x2,y1,y2,q=s.symbols('xP xQ yP yQ zeta')
cl=lambda a:s.factor(s.cancel(a))
K=(y1+y2)/(2*(x2-x1))
d1=lambda f:y1*s.diff(f,x1)+3*x1*x1*s.diff(f,y1)/2
d2=lambda f:y2*s.diff(f,x2)+3*x2*x2*s.diff(f,y2)/2
red=lambda f:cl(s.together(f).as_numer_denom()[0].expand().subs(y1*y1,x1**3-1).subs(y2*y2,x2**3-1))
checks={'literal_CM_kernel_curvature':red(d1(K)+d2(K)-(x2-x1)/4)==0}
checks['automorphism_CM_P_projection']=cl(4*((q*q*x2-q*x1)-q*q*(x2-x1))/(4*(q*q-q))-x1)==0
checks['automorphism_CM_Q_projection']=cl(4*((q*q*x2-q*x1)-q*(x2-x1))/(4*(q*q-q))-x2)==0
x,y,z,t,rho=s.symbols('x y z t rho')
U=x**3+y**3;W=x**3-y**3;qb=x*y
jac=s.det(s.Matrix([[s.diff(a,b) for b in [x,y,z]] for a in [U,qb,z]]))
checks['literal_U_q_z_physical_density']=cl(jac-3*W)==0
checks['source_y3_pair_unit']=cl((U/W-1)*jac/6-y**3)==0
kap=4*t**3/(2*t**3-1)
checks['full_CM_kappa_derivative']=cl(s.diff(kap,t)+12*t*t/(2*t**3-1)**2)==0
out={'status':'ACTUAL_CM_PROJECTORS_AND_WHOLE_SOURCE_DENSITY_NOT_CERTIFICATE','checks':checks,'check_count':len(checks),'CM_primitives':{'Omega':'(yQ+yP)/(2(xQ-xP))*(omegaQ-omegaP)','Omega_zeta':'Pullback under Q↦(zeta*xQ,yQ), omegaQ↦zeta*omegaQ, zeta²+zeta+1=0','JP':'4*(Omega_zeta-zeta²*Omega)/(zeta²-zeta), dJP=xP*omegaP*omegaQ','JQ':'4*(Omega_zeta-zeta*Omega)/(zeta²-zeta), dJQ=xQ*omegaP*omegaQ'},'actual_points':'P=(2^(1/3)t,rho),rho²=2t³−1; Q=(H^(1/3),sqrt(H−1)), both on y²=x³−1','full_original_source':'y³dx dy dz=−(U/W−1)*eta*dU*dR/18, eta=dt/rho,t=xy/z²,R=rho*z³; beta_original=−(U/W−1)*eta*dU*dR*thetaH/108','eta_R_binding':'eta*dU*dR=3z²*dt*dU*dz=−3*dU*dq*dz, all t-normal terms vanish in this equality by wedge dt, not by freezing physical variables.','actual_dual_Green_source':'omegaU−omegaW−kappa*dlog[(U+W)^3 R]/8=(3/16)(U/W−1)*dkappa; dkappa=−12t²dt/rho⁴','remaining':'A literal endpoint source-current equality must bind these actual CM projector densities and the full original Green source weight, retaining every H,C,b normal, diagonal/counterdiagonal pole, and infinity term.'}
assert all(checks.values()),checks
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
