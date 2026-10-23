from pathlib import Path
import json
import sympy as s
x,y,z,u,v,A,X=s.symbols('x y z u v alpha X')
H=1+x**6+y**6+z**6+x*y*z/2
C=x**3*z/2+x*y/3
p0=-3*z/2
K=1+x**6+z**6-s.Rational(3,4)*x**3*z**2
checks={'physical_linear_cancellation':s.expand(H+C*p0-y**6-K)==0}
f=u**6+A*u**3+1
Xu=u+1/u
for sign,label in ((1,'plus'),(-1,'minus')):
 Y=v*(u+sign)/u**2
 E=(Xu+sign*2)*(Xu**3-3*Xu+A)
 checks['quotient_'+label]=s.cancel((Y**2).subs(v**2,f)-E)==0
 checks['differential_'+label]=s.cancel(s.diff(Xu,u)/Y-(u-sign)/v)==0
checks['source_differential']=s.cancel((s.diff(Xu,u)/(v*(u+1)/u**2)+s.diff(Xu,u)/(v*(u-1)/u**2))/4-u/(2*v))==0
fplus=s.Poly((X+2)*(X**3-3*X+A),X)
a,b,c,d,e=fplus.all_coeffs()
I=12*a*e-3*b*d+c*c
J=72*a*c*e+9*b*c*d-27*a*d*d-27*b*b*e-2*c*c*c
j=6912*I**3/(4*I**3-J**2)
checks['varying_j_formula']=s.cancel(j+6912*(2*A+5)**3/((A-2)**3*(A+2)))==0
assert all(checks.values()),checks
out={'checks':checks,'j_plus':str(s.factor(j)),'status':'Exact source/quotient identities only; moving-kernel cancellation remains open.'}
Path(__file__).with_name('moving-pole-elliptic-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
