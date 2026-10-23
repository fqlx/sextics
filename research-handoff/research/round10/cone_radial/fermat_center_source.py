"""Literal source and normal expansion at X0=X1=0 in the cyclic target."""
from pathlib import Path
import sympy as s,yaml,json,time
HERE=Path(__file__).parent;start=time.monotonic()
rec=yaml.safe_load(Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec').read_text())
X0,X1,X2,Y0,Y1,Y2=s.symbols('X0 X1 X2 Y0 Y1 Y2');orig=(X0,X1,X2,Y0,Y1,Y2)
def build(name):return sum(s.Rational(c)*s.prod(q**e for q,e in zip(orig,ex))for c,ex in rec['polynomialData'][name]['terms'])
F,A=build('F'),build('A');x,v,w,a,b=s.symbols('x v w a b');c=s.Rational(5,7)
sub={X0:x,X1:v*x,X2:w,Y0:a,Y1:b,Y2:1};pull=s.expand(F.subs(sub));At=s.expand(A.subs(sub))
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
F0=w**6+S;normal=F0+c*B*w**3*x+R*x*x+c*w**3*x**3+Q*x**4+P*x**6
assert s.expand(pull-normal)==0
# Omega=Σ(-1)^i Zi dZ_0...omitZi...dZ_5. OnY2=1 the sign is−.
Jac=s.Matrix([x,v*x,w,a,b]).jacobian((x,v,w,a,b)).det();assert Jac==x
source_density=s.expand(-At*Jac);assert source_density==-a**3*x**4
assert s.expand(normal.subs({x:-x,w:-w},simultaneous=True)-normal)==0
out={'target':rec['id'],'chart':'Y2=1; X0=x,X1=v*x,X2=w,Y0=a,Y1=b','source_density_numerator':str(source_density),'orientation':'Standard Omega=sum_i(-1)^i Zi*dZ_except_i; Y2 index5 contributes minus; affine chart Jacobian is+x. Ordered volume dx,dv,dw,da,db.','F0':str(F0),'normal_coefficients':{str(k):str(s.Poly(normal,x).coeff_monomial(x**k))for k in range(7)},'literal_F_and_A_verified':True,'globalY_chart_action':'(x,w)->(-x,-w), while v,a,b fixed; full source density invariant. At center the fiber Wsign must be tracked together with the normal dx character.','source_normal_order':4,'first_naive_normal_primitive_order':5,'seconds':time.monotonic()-start}
(HERE/'fermat_center_source.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
