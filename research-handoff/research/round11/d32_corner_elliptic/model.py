from pathlib import Path
import sympy as S,json,pickle
P=Path(__file__).parent;v,z,U,Y=S.symbols('v zeta U Y');p=json.load(open('/workspace/research/round10/horizontal5/fresh/boundary/blowup_quadratic.json'));co={k:S.sympify(p[k],locals={'v':v,'zeta':z})for k in('A','B','C','D','E')};A,B,C,D,E=[co[k]for k in('A','B','C','D','E')];lam=5*z/7;G=(1+v**6)*(196*v**6+171);L=1+z*v
assert S.expand(B+926100*z*z*G)==0
assert S.expand(A*lam-3*B/2)==0 and S.expand(C+B*L)==0 and S.expand(E+S.Rational(20,63)*z*B*L)==0
q2=lam*(B-A*lam);H=S.expand(2*(2*A*lam-B)*(E-C*lam)-4*q2*C);J=S.expand((E-C*lam)**2+4*q2*D)
assert S.expand(H-S.Rational(10,63)*z*B*B*L)==0
PP=S.expand(D-S.Rational(20,189)*z*B*L*L);QQ=S.expand(S.Rational(625,3969)*z*z*B*L*L-2*lam*D)
assert S.expand(J-B*QQ)==0
AA=S.expand(H*H-4*B*B*J);assert S.expand(AA-8*lam*B**3*PP)==0
a2=-2*H;a4=AA;c4=16*(a2*a2-3*a4);Delta=S.expand(256*B*B*J*AA*AA)
assert S.expand(Delta-2048*lam*B**9*QQ*(8*lam)*PP**2)==0 # 256*64lambda²B9Q P²=16384lambda²...
# Quartic to elliptic map, exact as rational identity.
x=2*B*(Y+B*U*U)+H;yy=2*B*x*U
identity=S.expand(yy*yy-x*(x*x-2*H*x+AA));rem=S.rem(identity,S.Poly(Y*Y-B*B*U**4-H*U*U-J,Y).as_expr(),Y);assert S.expand(rem)==0
# differential under quartic relation: dx/yy=dU/Y.
dY=(4*B*B*U**3+2*H*U)/(2*Y);rat=S.cancel((S.diff(x,U)+S.diff(x,Y)*dY)*Y-yy);assert S.rem(S.together(rat).as_numer_denom()[0],Y*Y-B*B*U**4-H*U*U-J,Y)==0
model={'symbols':{'v':v,'zeta':z},'coefficients':co,'lambda':lam,'G':G,'L':L,'Hquartic':H,'Jquartic':J,'P14':PP,'Q14':QQ,'a2':a2,'a4':a4,'c4':c4,'Delta':Delta};(P/'model.pickle').write_bytes(pickle.dumps(model))
def expr(f):
 pp=S.Poly(S.expand(f),v,z);return '+'.join('('+str(c)+')*'+'*'.join(f'{x}^{e}'for x,e in zip((v,z),ex)if e)if any(ex)else '('+str(c)+')'for ex,c in pp.terms())
for name,phi in [('order4','zeta^2+1'),('order12','zeta^4-zeta^2+1')]:
 src=f'ring R=(0,zeta),(v),dp;minpoly={phi};\npoly B={expr(B)};poly G={expr(G)};poly P={expr(PP)};poly Q={expr(QQ)};poly a2={expr(a2)};poly a4={expr(a4)};\nprint("DEGREES");deg(P);deg(Q);deg(a2);deg(a4);\nprint("COPRIME AND SQUAREFREE");gcd(P,diff(P,v));gcd(Q,diff(Q,v));gcd(P,Q);gcd(P,G);gcd(Q,G);gcd(G,diff(G,v));\nprint("C4 DEGREE");deg(16*(a2*a2-3*a4));\nprint("DELTA DEGREE");deg(16*a4*a4*(a2*a2-4*a4));\nquit;\n';(P/f'check_{name}.sing').write_text(src)
out={'quartic':'Y²=B²U4+H U²+J','H':str(S.factor(H)),'J_factor':'B*Q14','P14':str(S.factor(PP)),'Q14':str(S.factor(QQ)),'Jacobian':'y²=x³−2H*x²+(H²−4B²J)*x','a4_factor':'8lambda*B³*P14','birational_map':'x=2B(Y+BU²)+H,y=2BxU','differential':'dx/y=dU/Y','candidate_fibers':'12III* atG,14I2 atP14,14I1 atQ14,I0*at∞','candidate_chi':13,'candidate_pg':12,'status':'Exact map/factor identities. Fiber coprimality and global compactification checks are separate.'};(P/'model.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
