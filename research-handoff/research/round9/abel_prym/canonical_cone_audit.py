"""Independent canonical-cone geometry/character and common-zero audit."""
from pathlib import Path
import pickle,json,time,sympy as s
HERE=Path(__file__).parent;start=time.monotonic()
p=pickle.load(open(HERE/'effective_schiffer.pickle','rb'));W,h,T,L,r,x,z=p['symbols'];c=s.Rational(5,7)
Z,R,u,v=s.symbols('Z R u v');Q=Z*u-R*R;G=Z**3+c*R**3+c*Z*R*v+L*u**3+r*u*u*v+v**3/x
image={Z:W**2,R:W*h,u:h**2,v:T}
assert s.expand(Q.subs(image))==0 and s.expand(G.subs(image)-p['curve'])==0
# A finite free basis over the two normal coordinates; monic leading terms
# in R,Z are R²,Z³ and hence coprime (all parameters are coefficients).
Gred=Z**3+c*(u+v)*R*Z+L*u**3+r*u*u*v+v**3/x
assert s.rem(s.Poly(s.expand(G-Gred),R),s.Poly(R*R-u*Z,R)).is_zero
A=c*(1+z);B=L+r*z+z**3/x;F6=W**6+A*W**3+B
assert s.cancel(s.discriminant(F6,W)-729*B**2*(A*A-4*B)**3)==0
D1=27*L*L+4*r**3*x
D2=-50824368*L**2-4321800*L*r*x+15625*L*x*x+1102500*L*x+12965400*L-7529536*r**3*x+30625*r*r*x*x+5762400*r*r*x-15625*r*x*x-918750*r*x-15625*x-826875
resultant=s.factor(s.resultant(p['N0'],p['N1'],z));extra=s.cancel(resultant/(4*x*D1**2*D2**2));assert s.denom(extra)==1
# Exact characteristic-zero transverse common zero on the smooth-curve part
# in universal canonical/source coordinates, not an asserted physical point.
Le=-s.Rational(5625+496125+10501974,194481)
sub={L:Le,r:0,x:1};nz=[s.Poly(p[k].subs(sub),z)for k in('N0','N1')];gcd=s.gcd(*nz);assert gcd.degree()==1
ze=s.solve(gcd.as_expr(),z)[0];point={**sub,z:ze}
assert p['N0'].subs(point)==0 and p['N1'].subs(point)==0
jac=s.det(s.Matrix([[s.diff(p[k],q)for q in(L,z)]for k in('N0','N1')])).subs(point)
assert jac!=0 and D1.subs(point)!=0 and D2.subs(point)!=0
prime=1000003
md=lambda q:int(s.Rational(q).p)*pow(int(s.Rational(q).q),-1,prime)%prime
Caff=7*p['curve'].subs({h:1,L:md(Le),r:0,x:1})
gb=s.groebner([Caff,s.diff(Caff,W),s.diff(Caff,T)],W,T,modulus=prime)
assert len(gb.polys)==1 and gb.polys[0].is_one
report={'canonical_embedding_exact':'[Z:R:u:v]=[W²:Wh:h²:T], image Q2=0,G3=C6. K_C=O_weighted(2), so O_C(1) of this embedding is the ordinary canonical bundle.','generic_cone_normality':'For smooth C, the affine CI cone is Cohen-Macaulay(S2), smooth off the vertex(R1), hence normal. Blowup of the vertex is Tot(O_C(-1)), smooth, with exceptional normal bundle K_C^-1 as an ordinary line bundle.','discrepancy':-2,'geometric_genus_defect':5,'finite_flat_basis':['1','Z','Z²','R','RZ','RZ²'],'finite_flat_degree':6,'basis_characters':[0,2,1,1,0,2],'finite_cover_discriminant':'729*u³*P²*(c²*u*(u+v)²-4P)³, P=L*u³+r*u²*v+v³/x',
 'equivariant_adjunction':'coordinate chars(Z,R,u,v)=(2,1,0,0), determinant0, quadricchar2,cubicchar0; K_C=O_C(1) tensor chi. Thus normal O(-1)=K_C^-1 tensor chi.','H0_K_char_counts':[1,2,1],'H1_O_char_counts':[1,1,2],'H1_O1_char_counts':[0,0,1],'R1_resolution_O_char_counts':[1,1,3],'higher_layers':'H1 O_C(n)=0 for n>=2 by Serre duality and degree; only n0,n1 contribute.',
 'target_character_binding':'Actual physical source has deck chi in H31; a serving divisor needs H20_chi, dual/conjugate to H2(O)_chi². Therefore the local rank3 chi² defect is the relevant candidate contribution. It is not a dimension3 H20 theorem by itself.',
 'common_zero_resultant':str(resultant),'extra_factor':str(extra),'smooth_transverse_universal_example':{'L':str(Le),'r':'0','x':'1','source_z':str(ze),'det_dN0N1_dLz_nonzero':str(jac),'curve_smooth_mod_prime':prime},
 'scope':'Normality/defect conclusions apply on transverse common-zero loci where the proper curve remains smooth. Components on D1D2 require separate analysis, and physical transversality is not inferred solely from this universal example. Global H20 additionally requires twists and Leray/conductor connecting maps plus every other boundary/resolution contribution. No source-serving or global extension is asserted.','seconds':time.monotonic()-start}
(HERE/'canonical_cone_audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
