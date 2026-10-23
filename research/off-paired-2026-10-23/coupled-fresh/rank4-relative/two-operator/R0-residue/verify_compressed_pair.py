import sympy as s
R,A,D,Lg,F=s.symbols('R A Dnum Lg Fsimple')
s1=(D-Lg)/A
left=Lg/R**2-(F/R-s1*A/R**2)
right=D/R**2-F/R
assert s.cancel(left-right)==0
# Principal A jet of the full fourth-order adjoint, with all coefficient
# derivatives allowed. At A=0, g2 starts D(0)*t^4/24; lower terms vanish.
t=s.symbols('t');b=s.symbols('b1:6');d=s.symbols('d0:5')
Aj=sum(b[k-1]*t**k for k in range(1,6))
Dj=sum(d[k]*t**k for k in range(5))
g2=Aj**4*Dj/(24*s.diff(Aj,t)**4)
jet=s.series(g2,t,0,5).removeO().expand()
assert s.expand(jet-d[0]*t**4/24)==0
assert s.diff(jet,t,4).subs(t,0)==d[0]
for k in range(4):assert s.diff(jet,t,k).subs(t,0)==0
print('Exact compressed R0-pair identity and complete fourth-order A interpolation passed.')
