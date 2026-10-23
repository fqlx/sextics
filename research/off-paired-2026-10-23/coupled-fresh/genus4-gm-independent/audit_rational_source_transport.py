"""Independent rational transport and coupled-residue identities.

Tests are polynomial identities in generic monomial exponents or rational
identities, with no coefficient-root branch dropped.
"""
import json
from pathlib import Path
import sympy as s

i,J,w,n,r,j,t=s.symbols('i J w n r j t')
T=1+w**3
k=3*i*w/(4*T)
A=k*k*T/J
R=A-1
S=k**6/R
Delta=3*R*S*w**3-3*R*S-8*R*w**3+R-S*w**3+2*S
N=9*i*i*w*w-16*J*T
L=256*T**5*N+729*i**6*J*w**6
v=64*J*w*N*T*T/(9*i*i*L)
h=3*i*w**3/(32*J*T*T*Delta)
checks={}
def check(name,expr):
 expr=s.cancel(expr)
 assert expr==0,(name,expr)
 checks[name]=True

check('physical_R_equals_N_over_16JT',R-N/(16*J*T))
check('rational_v_transport',v-w**3/(64*T**4*A*(1+S)))
alpha=54*i**3*w*T/(J*N)
check('actual_source_h_vw_over_v2',h*s.diff(v,w)/v**2-alpha)

# Under i^r J^j v^t, D has the eigenvalue delta.  Checking both
# independent exponent shifts is an operator-normal-form identity.
delta=6*t-2*r-2*j
m=delta-5
check('PE_pure_E2_shift',m*(m-1)-(delta-6)*(delta-5))
old_T=-r/s.Integer(3)-j/s.Integer(3)-2*m/s.Integer(3)-s.Rational(4,3)
check('PE_CEuler_shift',-old_T-(t+delta/2-2))
check('PD_D2_shift',2*j*(2*j-1)-(4*j*(j-1)+2*j))
old_A=-r/s.Integer(3)-4*j/s.Integer(3)-m/s.Integer(6)-s.Rational(5,6)
check('PD_CEuler_shift',-old_A-(t+j))
m3=delta-1
aa=-r/s.Integer(3)-4*j/s.Integer(3)-m3/s.Integer(6)-s.Rational(7,6)
bb=-r/s.Integer(3)-j/s.Integer(3)-m3/s.Integer(6)-s.Rational(1,6)
tt=-r/s.Integer(3)-j/s.Integer(3)-2*m3/s.Integer(3)-s.Rational(5,3)
check('P3_threeEuler_shift',-aa*bb*tt-(t+j+1)*t*(t+delta/2+1))

E0=i*s.diff(alpha,i)+2*J*s.diff(alpha,J)
check('source_residue_weight_minus1',E0+alpha)
P=-27*i**3*w*w/(16*J*J)-243*i**5*w/(128*J**3)
remainder=(2187*i**7*w*w/(128*J**3)-243*i**5/(8*J*J))/N
check('actual_full_Hermite_division',alpha-s.diff(P,w)-remainder)

# In the residue quotient Z=1, E0=-1, put u=J/i^2.  Let potential t=u^n.
# The two source weights cancel exactly for F=2 i^-1 t_u,
# G=(u*d_u+2)t.  The remaining ordinary third-order operator is recorded.
cancel_weight2=-2*n*(2*n-1)*(n+2)+2*n*(2*n-1)*(n+2)
check('PE_PD_unwanted_weight_cancels',cancel_weight2)
check('PE_PD_residue_lower_power',4*n*n*(2*n+1)-2*n*(4*n+2)*n)
check('PE_PD_residue_upper_power',-2*n*(n+1)*(n+2)+2*n*(n+2)*(n+1))
u=9*w*w/(16*T)
residue=32*T**3/(3*w*w*(2-w**3))
check('actual_residue_parameter_primitive',residue*s.diff(u,w)-6*(1/w+w*w))

out={
 'checks':checks,'count':len(checks),
 'operators':{
  'PE':'(D-6)(D-5)+A(Z+D/2-2)',
  'PD':'4J B^2+2B+A(Z+JB)',
  'P3':'A^3+v(Z+JB+1)Z(Z+D/2+1)',
  'relations':'[A,B]=[A,Z]=[B,Z]=0, D=6Z-2iA-2JB; oldA0=-Z-JB,oldB0=-Z,oldT0=-Z-D/2'},
 'coupled_residue_family':'u=J/i²,theta=u*d_u; F=2i^-1*t_u,G=(theta+2)t gives 2i^-1(theta+1)[u(4-u)t_uu+3(2-u)t_u]',
 'residue_primitive':'r du=6(w^-1+w²)dw, primitive=6 log(w)+2w³; logarithm retained, no rational closure claimed',
 'certificate':False,
}
Path(__file__).with_name('rational-source-transport-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
