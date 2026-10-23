#!/usr/bin/env python3
"""Literal next source-carrying j moment; no density derivative is omitted."""
import json
from pathlib import Path
import sympy as s
a,x,i,j,v=s.symbols('a x i j v');V=i*x*x+x+1
j_of_a=-a/x-V/(a*x)-x**5/(v*a**3)
j_a=s.diff(j_of_a,a);j_x=s.diff(j_of_a,x)
a_j=1/j_a;a_x=-j_x/j_a
psi1=x*x/(2*a*a)
psi2=x/(2*a)-x*V/(6*a**3)-3*x**7/(10*v*a**5)
# The third indefinite j integral contains -(log a)/2 dx. Replace it by
# +(x/2) da/a; its j derivative differs by a RATIONAL fiber differential.
R3=-V/(3*a*a)+(V*V/s.Integer(24)-9*x**6/(20*v))/a**4+2*V*x**6/(15*v*a**6)+9*x**12/(80*v*v*a**8)
psi3=R3+x*a_x/(2*a)
G3=x*a_j/(2*a)
Ej=lambda f:s.diff(f,a)*a_j
Dx=lambda f:s.diff(f,x)+s.diff(f,a)*a_x
checks={}
checks['literal_second_j_primitive']=s.cancel(Ej(psi2)-psi1)==0
checks['third_rational_j_primitive_mod_fiber_exact']=s.cancel(Ej(psi3)-psi2-Dx(G3))==0
# Independent direct implicit first moment derivative on descended curve.
Jbar=2*v*a*a+j*v*a*x-2*x**6/a**2
aj_implicit=-v*a*a*x/Jbar
checks['implicit_a_j_matches_inverse_rational_pencil']=s.cancel((aj_implicit-a_j).subs(j,j_of_a))==0
checks['literal_first_j_primitive']=s.cancel((s.diff(psi1,a)*aj_implicit-v*x**3/(a*Jbar)).subs(j,j_of_a))==0
# Total base lifts at fixed x; the flat implicit lift preserves [D,Ej]=Ej.
Q=v*(a*a+i*x*x+j*a*x+x+1)+x**6/a**2
ad=-a*(6*v*s.diff(Q,v)-2*i*s.diff(Q,i)-j*s.diff(Q,j))/Jbar
Et=lambda f:s.diff(f,j)+s.diff(f,a)*aj_implicit
Dt=lambda f:6*v*s.diff(f,v)-2*i*s.diff(f,i)-j*s.diff(f,j)+s.diff(f,a)*ad
for name,z in [('a',a),('i',i),('j',j),('v',v),('x',x)]:
 checks['commutator_D_Ej_'+name]=s.cancel((Dt(Et(z))-Et(Dt(z))-Et(z)).subs(j,j_of_a))==0
assert all(checks.values()),checks
out=Path(__file__).with_name('j-moment-hierarchy-results.json')
out.write_text(json.dumps({'status':'Literal rational next horizontal source current; actual density remains differentiated and no primitive claimed','curve':'a*y=x³; y²+v(a²+i*x²+j*a*x+x+1)=0','psi1':str(psi1)+' dx','psi2':str(psi2)+' dx','psi3':str(psi3)+' dx','third_fiber_correction':str(G3),'D':'6v partial_v-2i partial_i-j partial_j, at fixed x with implicit a lift','operator_relation':'partial_j[(2-D)Psi2]=(3-D)Psi1; partial_j[(3-D)Psi1]=(4-D)nu_b','source_transfer':'t partial_j²[(2-D)Psi2]=partial_j[t partial_j U2-t_j U2]+t_jj U2; every density derivative retained','residues':'Psi2 and U2 residue profiles have NOT been certified compact; retain finite and infinity components until audited','checks':checks,'certificate':False},indent=2)+'\n')
print('passed',len(checks),'exact groups; saved',out)
