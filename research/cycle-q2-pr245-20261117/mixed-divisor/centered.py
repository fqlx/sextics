"""Verify the centered mixed-current formulas. No rational solution is asserted.
Prepared for fqlx with OpenAI ChatGPT assistance.
"""
import contextlib,io,json
from pathlib import Path
with contextlib.redirect_stdout(io.StringIO()):
 import replay as r
s=r.s;y,p,b,T,I,J=r.y,r.p,r.b,r.T,r.I,r.J
H,P,K,Q,D,N=r.H,r.P,r.K,r.Q,r.D,r.N
f=b-y**2
omega=p/K;xi=T/b**4
G=I**2*y**2*p*(p+I)*b**14*T*(2*Q-T*s.diff(Q,T))/(24*K**3*Q**3)
assert s.cancel(G+I**2*D(omega,I)*D(D(xi,J),J)/12)==0
thetaIc=r.thetaI+s.Rational(3,4)/(I*b**2)
thetaJ=r.thetaJ
Oc=D(N,J)*thetaIc-D(N,I)*thetaJ
assert s.cancel(D(thetaIc,J)-D(thetaJ,I))==0
U=s.Function('U')(y,p,b,T,I,J)
V=lambda g:D(g,y)+2*y*D(g,b)
assert s.cancel(V(f))==0
Ay=U/f;Ab=2*y*U/f;AI=-N*thetaJ/f;AJ=N*thetaIc/f
# The arbitrary U and its actual implicit derivatives are retained.
assert s.cancel(D(Ay,y)+D(Ab,b)+D(AI,I)+D(AJ,J)-(V(U)+Oc)/f)==0
# Lagrange's trace identity: for deg A < n,
# Tr(A(z)/F'(z)) is the z^(n-1) coefficient of A divided by lc(F).
def lagrange_trace(A,F,z):
 q=s.Poly(F,z);a=s.Poly(A,z)
 assert a.degree()<q.degree()
 return s.cancel(a.nth(q.degree()-1)/q.LC())
assert lagrange_trace(-(6*I**5*T**3+b**8/2)/(2*b**2),P,T)==-3/(I*b**2)
assert lagrange_trace(b**7/2,P,T)==0
assert lagrange_trace(y**3*p**2,H,p)==y**3/(1+y**6)
assert lagrange_trace(p,H,p)==0
# Newton identities independently check that all displayed basis vectors are centered.
def companion(F,z):
 q=s.Poly(F,z).monic();n=q.degree();M=s.zeros(n)
 for j in range(n-1):M[j+1,j]=1
 for i in range(n):M[i,n-1]=-q.nth(i)
 return M
C=companion(H,p);B=companion(P,T)
u1=C+y/(6*(1+y**6))*s.eye(3)
u2=C*C+(-y**2/(12*(1+y**6)**2)+I*y/(3*(1+y**6)))*s.eye(3)
v1=B;v2=B*B+b**9/(2*I**6)*s.eye(4)
v3=B**3+3*(I*b**8/2-J*b**9)/(4*I**6)*s.eye(4)
for matrix in [u1,u2,v1,v2,v3]:assert s.cancel(s.trace(matrix))==0
# The scalar trace equation has a nonzero residue on b=y^2+f=0.
rfun=-s.Rational(3,4)*y**4*p*(p+I)/(I*K**3)
pt={I:s.Integer(1),J:s.Integer(2),y:s.Integer(1),p:s.Integer(-1)}
assert H.subs(pt)==0 and K.subs(pt)==s.Rational(11,2)
assert rfun.subs(pt)==0
assert D(rfun,y).subs(pt)==s.Rational(72,14641)
res=(D(rfun,y)/(4*y**2)-rfun/(4*y**3)).subs(pt)
assert res==s.Rational(18,14641)
report={'all_exact_checks':True,'scope':'Corrected current ansatz only; no solution of VU=fG-Oc and no protected primitive.',
 'current':['U/f','2*y*U/f','-N*b^7/(2*f*Q)','N*(-P_I/(2*b^2*T*Q)+3/(4*I*b^2))/f'],
 'identity':'div(A)=(V(U)+Oc)/f, V=D_y+2*y*D_b, Oc=D_J(N)*thetaIc-D_I(N)*thetaJ',
 'quartic_traces':{'thetaI':'-3/(I*b^2)','thetaJ':'0','thetaIc':'0'},
 'cubic_trace_N':'y^3/(1+y^6)','uncorrected_scalar_residue':str(res),
 'centered_basis_checks':5,'remaining_equation':'V(U)=f*G-Oc','remaining_equation_solved':False}
Path(__file__).with_name('centered-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
