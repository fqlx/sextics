import sympy as s
q,z,D=s.symbols('q z D')
B=-z/2
Ps=2*q**3+B*q+D;Pd=-2*q**3+B*q+D
Rs=(12*B*q*q-18*D*q+4*B*B)/(54*D*D+4*B**3)
Rd=(-12*B*q*q+18*D*q+4*B*B)/(-54*D*D+4*B**3)
alpha=z*q**3/(144*Ps*Pd)
base=s.factor(alpha-z/s.Integer(576)*(-s.diff(Ps,q)*Rs/Ps+s.diff(Pd,q)*Rd/Pd))
cross=s.factor(-z/s.Integer(576)*(s.diff(Ps,q)*Rd-s.diff(Pd,q)*Rs))
print('MC base coefficient:',base)
print('MC cross coefficient (1/sd):',cross)
print('MC Rs/s coeff:',s.factor(Rs/216))
print('MC Rd/d coeff:',s.factor(-Rd/216))
