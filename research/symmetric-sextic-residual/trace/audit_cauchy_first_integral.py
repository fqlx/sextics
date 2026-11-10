import sympy as s
v,ell,J,e,f,q0,q1=s.symbols('v ell J e f q0 q1',nonzero=True)
D=e**3-f**3*J/ell; E=e+f*v;Q=q0+q1*v;Einv=(e**2-e*f*v+f**2*v**2)/D
red=lambda P:s.Poly(s.rem(s.together(P),v**3+J/ell,v),v)
tr=lambda P:s.factor(3*red(P).nth(0))
assert s.factor(red(E*Einv).as_expr()-1)==0
assert tr(-ell*v**2/J)==0 and tr(-ell*v/J)==0
S1=tr(Q*(-ell*v**2/J)*Einv);S2=tr(Q*(-ell*v/J)*Einv)
assert s.factor(e*S2+f*S1)==0
print('S1=',s.factor(S1),'S2=',s.factor(S2));assert S1!=0
b,c,d,K=s.symbols('b c d K',nonzero=True)
I=(b**6+K)/(d**6+K);Vb=b**2*d**7/(d**6+K);Vd=b**7*d**2/(b**6+K)
assert s.factor(s.diff(I,b)*Vb+s.diff(I,d)*Vd)==0
# A second invariant c is constant, and on each leaf solve d^6 as a rational function of b^6.
X=s.symbols('X');d6=s.factor((b**6+K)/X-K)
assert s.factor((b**6+K)/(d6+K)-X)==0
print('PASS field trace S2=−f/e S1, explicit S1, and V(I)=0, V(c)=0; on I=X, d^6=(b^6+K)/X−K')
