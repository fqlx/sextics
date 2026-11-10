import sympy as S
v,u,A,B,C,p,q,r,J,ell,G,bd=S.symbols('v u A B C p q r J ell G bd',nonzero=True)
g=lambda x:A*x*x+B*x+C; P=lambda x:p*x*x+q*x+r; N=S.expand(g(v)*S.diff(P(v),v)-S.diff(g(v),v)*P(v));Na=S.expand(g(u)*S.diff(P(v),v)-(2*A*u+B)*P(v));Q=S.cancel((N-Na)/(v-u));assert S.denom(Q)==1
E=2*r+q*v;vstar=-2*r/q;alpha=S.factor(-N.subs(v,vstar)/((u-vstar)*Q.subs(v,vstar)));L=S.cancel((N+alpha*(u-v)*Q)/E)
assert S.denom(L).free_symbols.isdisjoint({v});assert S.Poly(L,v).degree()<=1
# Tr(vQ) = 0 in the cubic, so the added weight contributes zero source.
red=lambda x:S.Poly(S.rem(S.together(x),v**3+J/ell,v),v)
assert red(v*Q).nth(0)==0
F=ell*u**3+J;invuv=ell*(u*u+u*v+v*v)/F
assert S.factor(3*red(-2*bd*F*L*E*v*invuv/(3*J*G**3)).nth(0)-2*bd*N.subs(v,u)/G**3)==0
aa,bb=S.symbols('aa bb'); LL=S.Poly(L,v); l0,l1=LL.nth(0),LL.nth(1)
T0=l1*aa; T1=-ell*l0*bb/J;T2=-ell*(l0*aa+l1*bb)/J
beta=-ell*(aa*v*v+bb*v)/J
assert all(S.factor(red(L*beta).nth(i)-t)==0 for i,t in enumerate((T0,T1,T2)))
current=3*J/G**3*(3*ell*u*u*(T0+T1*u+T2*u*u)-3*F*(T1+u*T2))
assert S.factor(3*red(3*J*F*L*beta*invuv/G**3).nth(0)-current)==0
print('PASS E-free weight exact source trace and current quotient identity.')
