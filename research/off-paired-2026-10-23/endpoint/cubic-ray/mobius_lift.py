"""Exact universal Mobius primitive and the physical divergence defect.

A rational solution of K(h)=N2(J)/J^2 would close this sufficient current.
No rational h is assumed or produced.
"""
import json
from pathlib import Path
import sympy as S
from finite_connection import s,H,B,C,D,T,f,invT,MH,MB,MC,source,reduce

checks=[]
def check(name,expr):
 assert S.cancel(expr)==0,(name,S.factor(expr));checks.append(name)

W2H=-2*B**2/(3*C);W2B=3*H
W2=lambda expr:S.diff(expr,H)*W2H+S.diff(expr,B)*W2B
F=(3*C*s**2-B)*invT**3/10
Fvec=S.Matrix([27*B**2*C*H/(5*D**2),-3*C*(8*B**3-27*C*H**2)/(10*D**2)])
check('F-tracezero-reduction',reduce(F)-Fvec[0]*s-Fvec[1]*(s**2+2*B/(3*C)))
check('discriminant-T-identity',reduce(D-T**2*(T+3*B)))
check('W2-discriminant',W2(D))
ds=s**2+2*B/(3*C)
check('W2-T',reduce(W2(T)+S.diff(T,s)*ds-s*T))
check('W2-source-field',reduce(W2(F)+S.diff(F,s)*ds-B*s*invT**3))
out=(Fvec.diff(H)*W2H+Fvec.diff(B)*W2B+(MH*W2H+MB*W2B)*Fvec-source)
for i in range(2):check('W2-source-basis-'+str(i),out[i])

x,a,u,v=S.symbols('x a u v');coords=[x,a,u,v]
Hp=1+x**6+a**6;Cp=1+u**6+v**6;Bp=x*u/2+x**3*a*u*v/2+x*a*v/3
gradient=lambda p:S.Matrix([S.diff(p,q)for q in coords])
dH,dB,dC=map(gradient,[Hp,Bp,Cp])
J=dH[0]*dB[1]-dH[1]*dB[0]
Q=dB[2]*dC[3]-dB[3]*dC[2]
K=S.Matrix([dH[1]*Q,-dH[0]*Q,dC[3]*J,-dC[2]*J])
N2=-2*Bp**2/(3*Cp)*S.Matrix([dB[1],-dB[0],0,0])+3*Hp*S.Matrix([-dH[1],dH[0],0,0])
div=lambda V:sum(S.diff(V[i],coords[i])for i in range(4))
for name,p,target in [('H',Hp,-2*Bp**2*J/(3*Cp)),('B',Bp,3*Hp*J),('C',Cp,0)]:check('N2-'+name,N2.dot(gradient(p))-target)
check('N2-divergence',div(N2))
for name,p in [('H',Hp),('B',Bp),('C',Cp)]:check('K-'+name,K.dot(gradient(p)))
check('K-divergence',div(K))
# Quotient-rule identity is checked without expanding the large denominator.
numerator=N2.dot(gradient(J))
check('V0-divergence-numerator',sum(S.diff(N2[i],coords[i])*J-N2[i]*S.diff(J,coords[i])for i in range(4))+numerator)
data={'check_count':len(checks),'checks':checks,
 'F0_field':'(3*C*s^2-B)/(10*(B+3*C*s^2)^3)',
 'F0_basis':[str(z)for z in Fvec],
 'W2':{'H':str(W2H),'B':str(W2B),'C':'0'},
 'physical_H':str(Hp),'physical_B':str(Bp),'physical_C':str(Cp),
 'J':str(S.factor(J)),'Q':str(S.factor(Q)),
 'N2':[str(S.factor(z))for z in N2],
 'K':[str(S.factor(z))for z in K],
 'divergencefree_lift_obligation':'K(h)=N2(J)/J^2',
 'conditional_current':'F0*(N2/J+h*K)',
 'relative_density':'omega=du/(C_v*J), omega(K)=1',
 'relative_equation':'d_fiber h = (N2(J)/J^2)*omega',
 'status':'universal source primitive and explicit physical defect; rational h remains open'}
Path(__file__).with_name('mobius-lift-results.json').write_text(json.dumps(data,indent=2))
print('Passed',len(checks),'exact identities')
