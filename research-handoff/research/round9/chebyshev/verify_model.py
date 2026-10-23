from pathlib import Path
import sympy as S,pickle,json
from flint import nmod_poly
H=Path(__file__).parent;k,s,t,a1,a0,b2,b1,b0,c0,tau,Z=S.symbols('k s t a1 a0 b2 b1 b0 c0 tau Z')
N=a1*s+b2;tt=-N/(3*s*s);c2=3*s*s*t+a1*s+b2;c1=3*s*t*t+a1*t+a0*s+b1;cc0=t**3+a0*t+b0
P=9*s**6+3*a0*s**4+3*b1*s**3+a1*b2*s+b2*b2
assert S.cancel((c1+3*s**3).subs(t,tt)-P/(3*s**3))==0
assert S.cancel(27*s**6*cc0.subs(t,tt)+N**3+9*a0*s**4*N-27*b0*s**6)==0
V=k*k-4;Q=k**3-3*k-tau
R1=k**3-3*k;Y1=(k*k-1)*Z
assert S.expand((R1*R1-4)-(k*k-4)*(k*k-1)**2)==0
R2=(k**3-4*tau)/V;fac=(k**3-12*k+8*tau)/V**2
assert S.cancel(S.diff(R2,k)-k*fac)==0
assert S.cancel((fac**2*s**3*V*Q)-s**3*(R2**3-27*R2+27*tau))==0
# x=sR2,y=fac Z, tau=-c0/s^3
assert S.cancel(s**3*(R2**3-27*R2+27*tau)-((s*R2)**3-27*s*s*(s*R2)-27*c0)).subs(c0,-tau*s**3)==0
# finite flat algebra / module identities as multiplication operators
B=S.zeros(6);C=S.zeros(6)
# basis 1,s,s2,s3,u,u2
B[:,0]=S.Matrix([0,1,0,0,0,0]);B[:,1]=S.Matrix([0,0,1,0,0,0]);B[:,2]=S.Matrix([0,0,0,1,0,0]);B[:,3]=S.Matrix([0,-b1/3,-a0/3,0,-a1/9,-S.Rational(1,9)]);B[:,4]=S.Matrix([b2,0,0,0,0,0]);B[:,5]=S.Matrix([0,0,0,0,b2,0])
C[:,0]=S.Matrix([0,0,0,0,1,0]);C[:,1]=S.Matrix([b2,0,0,0,0,0]);C[:,2]=S.Matrix([0,b2,0,0,0,0]);C[:,3]=S.Matrix([0,0,b2,0,0,0]);C[:,4]=S.Matrix([0,0,0,0,0,1]);C[:,5]=S.Matrix([-3*b1*b2,-3*a0*b2,0,-9*b2,0,-a1])
assert B*C==b2*S.eye(6) and C*B==b2*S.eye(6)
assert C*C+a1*C+3*b1*B+3*a0*B**2+9*B**4==S.zeros(6)
old=pickle.loads(Path('/workspace/research/round6/k3_normalform/lambda_gm.pickle').read_bytes());ok,oq,oh=[old['symbols'][x]for x in['k','q','h']];q,h=S.symbols('q h');A=old['scaled']['A'].subs({ok:k,oq:q,oh:h});BB=old['scaled']['B'].subs({ok:k,oq:q,oh:h});al=old['scaled']['A_lambda'].subs({ok:k,oq:q,oh:h});bl=old['scaled']['B_lambda'].subs({ok:k,oq:q,oh:h});co={a1:S.expand(A).coeff(k,1),a0:A.subs(k,0),b2:S.expand(BB).coeff(k,2),b1:S.expand(BB).coeff(k,1),b0:BB.subs(k,0)};jets={a1:S.expand(al).coeff(k,1),a0:al.subs(k,0),b2:S.expand(bl).coeff(k,2),b1:S.expand(bl).coeff(k,1),b0:bl.subs(k,0)}
physicalP=S.expand(P.subs(co));physicalt=S.cancel(tt.subs(co));
p=173;found=None
md=lambda c:int(S.Rational(c).p)%p*pow(int(S.Rational(c).q)%p,-1,p)%p
for hv in range(3,p):
 pp=S.Poly(physicalP.subs({q:2,h:hv}),s);fp=nmod_poly([md(pp.nth(i))for i in range(7)],p)
 facs=fp.factor()[1]
 if len(facs)==1 and facs[0][0].degree()==6 and facs[0][1]==1:found={'prime':p,'q':2,'h':hv,'irreducible_slope_coefficients':[int(fp[i])for i in range(7)]};break
assert found
H.joinpath('physical_model.pickle').write_bytes(pickle.dumps({'symbols':{'q':q,'h':h,'s':s,'t':t,'k':k},'coefficients':{str(a):v for a,v in co.items()},'jets':{str(a):v for a,v in jets.items()},'P':physicalP,'t':physicalt,'irreducible_witness':found}))
out={'slope_identity':'c1+3s3=P(s)/(3s3) after t=−(a1s+b2)/(3s2)','first_quotient':{'R':'k3−3k','Y':'(k2−1)Z','equation':'Y²=s3(R²−4)(R−tau)','differential':'dR/Y=3dk/Z'},'second_quotient':{'R':str(R2),'Y_factor':str(fac),'x':'sR','y':'Y','equation':'y²=x³−27s²x−27c0','differential':'dx/y=s*k*dk/Z relative to the base; no sqrt(s)'},'trace_projectors':{'first':'trace(k)=0 for k3−3k−R1; f1_*(dk/Z)=dR1/Y1 and f1_*(kdk/Z)=0','second':'trace(1/k)=0 for k3−R2 k2+4R2−4tau; f2_*(dk/Z)=0 and f2_*(kdk/Z)=3/s dx/y'},'partial_normalization':'su=b2, u²+a1u+3b1s+3a0s²+9s4=0; basis1,s,s2,s3,u,u2','cleared_Weierstrass':'X=s²x,Y=s³y: Y²=X³−27s6X+(a1s+b2)³+9a0s4(a1s+b2)−27b0s6','minimal_line':'Lraw=pi*O(6,6); subtract Dgood=(s0,u=−a1). Further normalization/minimality still required.','irreducibility_witness':found,'status':'Exact maps, relative differentials and finite-algebra checks. No global H20 or original Gysin certificate asserted.'};H.joinpath('verified_model.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
