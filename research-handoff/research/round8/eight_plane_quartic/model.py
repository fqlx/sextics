from pathlib import Path
import sympy as s,pickle,json,yaml,hashlib,time
root=Path(__file__).parent;start=time.monotonic()
X=s.symbols('X0:3');Y=s.symbols('Y0:3')
ell=[sum((j+i+1)*X[j]for j in range(3))/7 for i in range(3)]
m=[sum((2*j+i+1)*Y[j]for j in range(3))/11 for i in range(3)]
n=[sum((j+1)**(i+1)*X[j]for j in range(3))/13 for i in range(3)]
o=[sum((j+2)**(i+1)*Y[j]for j in range(3))/17 for i in range(3)]
F=sum(x**6 for x in X+Y)+sum(s.Rational(5,p)*(X[i]**2+Y[i]**2)*(ell[i]**3*n[i]+m[i]**3*o[i]+ell[i]**2*o[i]**2)for i,p in enumerate([7,11,13]))
recpath=Path('/workspace/sextics/data/eight-plane-configuration/instance.rec')
rec=yaml.safe_load(recpath.read_text());original=s.sympify(rec['F'],locals=dict(zip([str(z)for z in X+Y],X+Y)))
assert s.expand(F-original)==0
A=X[0]**3*Y[0]**3;assert s.expand(A-s.sympify(rec['A'],locals=dict(zip([str(z)for z in X+Y],X+Y))))==0
k,z,u1,u2,v1,v2,eps=s.symbols('k z u1 u2 v1 v2 eps')
u=[1,u1,u2];v=[1,v1,v2];U=[k*z*a for a in u];V=[k*a for a in v]
XX=[(a+b)/2 for a,b in zip(U,V)];YY=[(a-b)/(2*s.I)for a,b in zip(U,V)]
J=s.factor(s.Matrix(XX+YY).jacobian([k,z,u1,u2,v1,v2]).det())
assert J==s.I*z*z*k**5/8
Anew=s.factor(A.subs(dict(zip(X+Y,XX+YY)),simultaneous=True));N=(z*z-1)**3
assert s.expand(Anew-s.I*k**6*N/64)==0
Fnew=s.expand(F.subs(dict(zip(X+Y,[a.subs(k,1)for a in XX+YY])),simultaneous=True))
poly=s.Poly(Fnew,z);assert poly.degree()==5 and poly.nth(0)==0
G=s.Poly(s.cancel(Fnew/z),z);assert G.degree()==4
g=[s.factor(G.nth(i))for i in range(5)]
assert s.expand(sum(g[i]*z**i for i in range(5))*z-Fnew)==0
# The global Y sign swaps the disjoint planes and the two shape coordinates.
sw={u1:v1,u2:v2,v1:u1,v2:u2}
for i in range(5):assert s.expand(g[i]-g[4-i].subs(sw,simultaneous=True))==0
assert s.cancel(Anew*J/k**11+z*z*N/512)==0
# Actual normal deformation does not preserve the planes.  Keep its exact
# transformed Laurent term rather than differentiating a frozen quartic.
AA=s.I*N/64;JJ=s.I*z*z/8;Gsymbol=s.symbols('Gsymbol')
normal_source=s.diff(JJ/(z*Gsymbol+eps*AA),eps).subs(eps,0)*(-1)
assert s.cancel(normal_source+N/(512*Gsymbol**2))==0

symbols=dict(z=z,u1=u1,u2=u2,v1=v1,v2=v2,eps=eps)
packet=dict(symbols=symbols,F=F,A=A,G=G.as_expr(),coefficients=g,N=N,
            projective_chart_Jacobian=s.I*z*z/8,source_factor=-s.Rational(1,512),
            normal_deformation=z*G.as_expr()+eps*s.I*N/64,
            source='-N dz wedge du1 du2 dv1 dv2/(512 G^2)',
            instance_rec_sha256=hashlib.sha256(recpath.read_bytes()).hexdigest())
(root/'model.pickle').write_bytes(pickle.dumps(packet))
good={u1:1,u2:2,v1:3,v2:5};GG=s.Poly(G.as_expr().subs(good),z)
mod=lambda x:int(s.numer(x))%101*pow(int(s.denom(x)),-1,101)%101
from flint import nmod_poly
gf=nmod_poly([mod(GG.nth(i))for i in range(5)],101)
assert gf.degree()==4 and gf.gcd(gf.derivative()).degree()==0
ans=dict(target='eight-plane-configuration',instance_rec_sha256=packet['instance_rec_sha256'],
         exact_record_bound=True,full_coordinate_Jacobian=str(J),A_transformed=str(Anew),
         source_factor='-1/512',quartic_coefficients=[str(a)for a in g],
         coefficient_term_counts=[len(s.Poly(a,u1,u2,v1,v2).terms())for a in g],
         actual_normal_deformation='z*G+eps*i*(z^2-1)^3/64',
         good_base={str(a):b for a,b in good.items()},good_prime=101,
         good_quartic_coefficients=list(map(int,gf)),good_quartic_squarefree=True,
         seconds=time.monotonic()-start,
         scope='Exact source model, not a primitive or coniveau assertion.')
(root/'model.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps({k:v for k,v in ans.items()if k!='quartic_coefficients'},indent=2))
