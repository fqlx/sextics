from pathlib import Path
import json
import sympy as s
z,U,K,t,p=s.symbols('z U K t p')
q=[z,U,K,t]
H=1+z*z+t
B=U/s.Integer(2)+K/3+z*U*K/2
C=z**-2+U**6+K**6/t
f=H+B*p+C*p**3
g=s.diff(f,p)
rho=1/(18*t*z*z)
pi=s.Matrix([[0,3*z*z,0,0],[-3*z*z,0,0,0],[0,0,0,6*t],[0,0,-6*t,0]])
def basebr(F,G):return (s.Matrix([s.diff(F,x) for x in q]).T*pi*s.Matrix([s.diff(G,x) for x in q]))[0]
A=36*(z**3*U**5-K**5)
DD=9*z*z*U**6*K+3*(1+z*K)/z-(2+3*z*U)*K**6/t
E=3*z**3+3*z**4*K-2*t-3*t*z*U
Q=3*p*p*A+2*p**3*DD+E
checks={
'HC_bracket':s.factor(basebr(H,C)-A)==0,
'BC_bracket':s.factor(basebr(B,C)-DD)==0,
'HB_bracket':s.factor(basebr(H,B)-E)==0,
'fg_bracket':s.factor(basebr(f,g)-Q)==0,
}
N=pi*s.Matrix([s.diff(f,x) for x in q])
checks['N_preserves_ambient_f']=s.factor(sum(N[i]*s.diff(f,q[i]) for i in range(4)))==0
checks['N_partial_divergence']=s.factor(sum(s.diff(rho*N[i],q[i]) for i in range(4)))==0
checks['N_implicit_divergence']=s.factor(-sum(s.diff(f,q[i])*s.diff(N[i],p) for i in range(4))+Q)==0
# The product rule uses only N(g)=-Q and div_rho N=-Q/g.
Ag,Ng,gg,QQ,AA,NAA=s.symbols('Ag Ng g Q A NA')
checks['actual_current_product_rule']=s.expand(NAA/gg**2-2*AA*(-QQ)/gg**3+AA*(-QQ/gg)/gg**2-(AA*QQ/gg**3+NAA/gg**2))==0
checks['partial_ambient_divergence']=s.expand(-NAA/gg-AA*QQ/gg**2+AA*QQ/gg**2+NAA/gg)==0
# Independent coefficient-level reduction for the p-current criterion.
HH,BB,CC,pp,VH,VB,VC,dd=s.symbols('H B C p VH VB VC d')
ff=HH+BB*pp+CC*pp**3
ggg=BB+3*CC*pp**2
Delta=4*BB**3+27*CC*HH**2
checks['cubic_discriminant_identity']=s.rem(s.expand(Delta-ggg**2*(ggg+3*BB)),ff,pp)==0
checks['source_low_pole_identity']=s.rem(s.expand(BB*pp*Delta-(BB*BB*pp-3*BB*HH)*ggg**2),ff,pp)==0
expected=(-VH+HH*VC/CC-3*HH*dd+pp*(-VB+BB*VC/CC-2*BB*dd))/ggg
raw=-(VH+VB*pp+VC*pp**3)/ggg+pp*dd
checks['p_current_contact_formula']=s.rem(s.together(raw-expected).as_numer_denom()[0],ff,pp)==0
# Independent coordinate Jacobian and exact Piola vector check.
x,a,y,Y1,Y2=s.symbols('x a y Y1 Y2')
coords=[x**3,Y1/(x*y),a*Y2/(x*y),a**6,x*x*y*y]
old=[x,a,y,Y1,Y2]
M=s.Matrix([[s.diff(c,v) for v in old] for c in coords])
J=36*a**6*x*x/y
checks['coordinate_jacobian']=s.factor(M.det()-J)==0
Vz,VU,VK,Vt,Vp=s.symbols('Vz VU VK Vt Vp')
VV=s.Matrix([Vz,VU,VK,Vt,Vp])
WW=s.Matrix([12*a**6*Vz/y,6*a*x*x*Vt/y,18*a**6*Vp/y**2-12*a**6*Vz/x,36*a**6*x**3*VU+18*a**6*Y1*Vp/y**3,36*a**5*x**3*VK+Y2*(18*a**6*Vp/y**3-6*x*x*Vt/y)])
for i,v in enumerate(M*WW-J*VV):checks[f'piola_coordinate_{i}']=s.factor(v)==0
newA=p*p/(36*t*z*z)
checks['source_pullback']=s.factor(J*newA.subs({z:x**3,t:a**6,p:x*x*y*y})-y**3)==0
out={'checks':checks,'status':'Actual Hamiltonian first current plus exact correction and original-coordinate Piola interface; no complete current.'}
assert all(checks.values()),checks
Path(__file__).with_name('cubic-poisson-witness-interface-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
