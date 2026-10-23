"""Exact bookkeeping receipt for the stopped Klein line-channel exploration."""
import json
import sympy as s
x,y,z,U,V,W,a,b,d,t=s.symbols('x y z U V W a b d t')
M=s.Matrix([[2,1,-1],[-1,2,1],[1,-1,2]])
assert M.det()==14
assert s.Matrix([[2,-1,-1]])*M.inv()==s.Matrix([[s.Rational(4,7),-s.Rational(5,7),s.Rational(1,7)]])
u=x*x*y/z;v=y*y*z/x;w=z*z*x/y
assert s.cancel(u*u*w+u*v*v+v*w*w-(x**5*y+y**5*z+z**5*x))==0
assert s.cancel(u**4*w/v**5-(x*x/y/z)**7)==0
assert s.cancel((a*t/b)**4*(a*(1-t)/d)-a**5*t**4*(1-t)/(b**4*d))==0
# Relative BWB output ranks and P2 Euler characteristics.
chi=lambda degree:(degree+2)*(degree+1)//2
bundles={0:{0:1},1:{0:1,-2:3},2:{-2:6,-4:3,-6:1},4:{-4:6,-6:8,-8:6}}
ranks={k:sum(B.values()) for k,B in bundles.items()}
assert ranks=={0:1,1:4,2:10,4:20}
assert ranks[0]-ranks[1]+ranks[2]+ranks[4]==27
euler=sum(((-1)**k)*sum(n*chi(deg) for deg,n in B.items()) for k,B in bundles.items())
assert euler==243
print(json.dumps({'determinant':14,'target_character':3,'line_curve_genus':3,'holomorphic_differential_orders':[3,0,1],'fiber_euler':27,'conditional_raw_line_scheme_h1':1,'conditional_raw_line_scheme_euler':euler,'identities':'PASS','scope':'No line-scheme smoothness, twisted irregularity, Gysin, or certificate claim.'},indent=2))
