from pathlib import Path
exec(open(Path(__file__).resolve().parent / 'audit_cauchy_Efree.py').read())
b,cc,d,t=S.symbols('b cc d t');z=S.Integer(4);L0=S.Integer(130);R=S.Integer(2)*(1+cc**6)
X=1+2*b-u;Y=cc**2+2*cc*d-z*u
H=6*u+6*u*u+6*z*cc**4*u+6*z*z*cc**2*u*u+(X*X*Y+2*X*Y*Y)/7
Ft=b**6+d**6+R+L0*u**3+t*H;gt=S.diff(Ft,u);Gpoly=S.Poly(gt,u)
Lphysical=L.subs({A:Gpoly.nth(2),B:Gpoly.nth(1),C:Gpoly.nth(0),p:z,q:-(cc**2+z),r:cc**2}, simultaneous=True)
Lc=S.Poly(S.cancel(Lphysical),v); l0,l1=Lc.nth(0),Lc.nth(1);J0=b**6+d**6+R;F0=J0+L0*u**3;g0=3*L0*u*u

def curr(a,h):
 t0=l1*a;t1=-L0*l0*h/J0;t2=-L0*(l0*a+l1*h)/J0
 return 3*J0/gt**3*(g0*(t0+t1*u+t2*u*u)-3*F0*(t1+u*t2))
xb=-(cc**2+z)*b*b*d/(18*L0*(d**6+R)); yb=cc**2*b*b*d/(9*L0*R)
xd=-(cc**2+z)*b*d*d/(18*L0*(b**6+R)); yd=cc**2*b*d*d/(9*L0*R)
cb=curr(xb,yb); cd=curr(xd,yd)
def mod(x):
 x=S.factor(x);return int(S.numer(x))*pow(int(S.denom(x))%101,-1,101)%101
pt={b:100,cc:30,d:74,u:85,t:5};gval=gt.subs(pt);assert mod(Ft.subs(pt))==0 and mod(gval)!=0
# Evaluate chain rule after partial differentiation on independent b,u and d,u coordinates.
def tang(expr,var):return S.diff(expr,var).subs(pt)-S.diff(Ft,var).subs(pt)*S.diff(expr,u).subs(pt)/gval
div=tang(cb,b)+tang(cd,d);P0=(1-u)*(cc**2-z*u);target=2*b*d*(gt*S.diff(P0,u)-S.diff(gt,u)*P0)/gt**3
val=S.factor(target.subs(pt)-div); rem=int(S.numer(val))*pow(int(S.denom(val))%101,-1,101)%101;print('actual t=5 defect mod101=',rem);assert rem!=0
for name,expr in [('l0',l0),('l1',l1),('current_b',cb),('current_d',cd),('gt',gt),('J0',J0),('F0',F0),('K',R)]:
 val2=S.factor(expr.subs(pt)); assert mod(S.denom(val2))!=0,(name,'denominator');
 if name in ('gt','J0','F0','K'):assert mod(val2)!=0,(name,'nonunit')
 print(name,'unit checks pass')
