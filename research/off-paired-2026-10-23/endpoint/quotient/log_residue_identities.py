"""Exact source-carrying conic-log residue currents, including vertical correction.

No fixed physical source is integrated unless d_g can be corrected to its
required constant. The identities retain all rational normal derivatives.
"""
import sympy as s,json
from pathlib import Path
u,v,z=s.symbols('u v z');vs=[u,v,z]
H=1+u**6/v**2+v**2+z**6+u*z/2;C=u**3*z/(2*v)+u/3;pole=-3*z/2;L=H+pole*C;F=L**2-4*pole**6
B=s.Matrix([s.diff(L,q)-3*L*s.diff(pole,q)/pole for q in vs]);dC=s.Matrix([s.diff(C,q)for q in vs]);dL=s.Matrix([s.diff(L,q)for q in vs]);dpole=s.Matrix([s.diff(pole,q)for q in vs]);dF=s.Matrix([s.diff(F,q)for q in vs])
chi={'x':s.Matrix([1/u,-1/(3*v),0]),'y':s.Matrix([0,1/(3*v),0]),'z':s.Matrix([0,0,1/z])}
checks=[];out={}
for name,dc in chi.items():
 V=B.cross(dc).applyfunc(s.cancel);VL=s.cancel(V.dot(dL));Vs=s.cancel(V.dot(dpole));div=s.cancel(sum(s.diff(a,q)for a,q in zip(V,vs)))
 assert s.cancel(VL-3*L*Vs/pole)==0;checks.append(name+'-conic-tangent')
 assert s.cancel(div-V.dot(dF)/(2*F))==0;checks.append(name+'-residue-closure')
 assert s.cancel(div-3*Vs/pole)==0;checks.append(name+'-log-normal-divergence')
 K=s.cancel(V.dot(dC)-2*C*Vs/pole)
 out[name]={'V':[str(s.factor(a))for a in V],'source_multiplier':str(s.factor(K)),'vertical_multiplier':str(s.factor(Vs/pole))}
Kx=u**2+z**5/(3*v)-(1+u**6/v**2)/(3*v*z)+v/z+u**3*z/(12*v**2)
assert s.cancel(s.sympify(out['x']['source_multiplier'])-Kx)==0;checks.append('physical-Kx')
assert s.cancel(s.sympify(out['x']['V'][2])+2*v/u)==0;checks.append('physical-Vx-z')
# Direct raw differential identity, after clearing (p-s)^2 Z^3.
p,h,c,r,A,Q=s.symbols('p H C r A Q');S=h+c*p;f=S**2-4*p**6
VH=A*(3*h+2*r*c)-r*Q;VC=Q;Vr=r*A;Div=3*A
lhs=-VH*S*(p-r)-VC*p*S*(p-r)+Vr*f+Div*f*(p-r)
dg=Q-2*c*A
rhs=-dg*S*(p-r)**2+A*(r*f+p*(p-r)*s.diff(f,p)/2)
assert s.expand(lhs-rhs)==0;checks.append('raw-source-plus-vertical-exact')
# Conic parametrization, where rparam=(L+T)/(2s0^3 z^3).
w,ss,zz=s.symbols('rparam s0 z0');Le=ss**3*zz**3*(w+1/w);Te=ss**3*zz**3*(w-1/w)
assert s.cancel(Te**2-Le**2+4*(ss*zz)**6)==0;checks.append('conic-Gm-parametrization')
assert s.cancel(s.diff(Le,w)/Te-1/w)==0;checks.append('conic-log-differential')
assert s.cancel(s.diff(Le,zz)-3*Le/zz)==0;checks.append('conic-log-horizontal')
out={'checks':checks,'count':len(checks),'currents':out,'raw_identity':'div_connection(V beta_s)=d_g nabla_H omega0 -(V(s)/s)*d_p[p/((p-s)Z)]','status':'actual source multiplier d_g; physical constant-source correction remains open'}
Path(__file__).with_name('log-residue-identities-results.json').write_text(json.dumps(out,indent=2));print('Passed',len(checks),'exact identities')
