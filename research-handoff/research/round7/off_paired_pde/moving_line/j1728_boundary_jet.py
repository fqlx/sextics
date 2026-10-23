from pathlib import Path
import pickle,sympy as s,json
P=pickle.load(open('/workspace/research/round6/k3_normalform/lambda_gm.pickle','rb'))
k,q,h=[P['symbols'][x]for x in ('k','q','h')]
A,B,Al,Bl=[P['scaled'][x]for x in ('A','B','A_lambda','B_lambda')]
a1=s.Poly(A,k).nth(1);a0=s.Poly(A,k).nth(0);b1=s.Poly(B,k).nth(1);b0=s.Poly(B,k).nth(0)
a1l=s.Poly(Al,k).nth(1);a0l=s.Poly(Al,k).nth(0);b1l=s.Poly(Bl,k).nth(1);b0l=s.Poly(Bl,k).nth(0)
assert s.Poly(Bl,k).nth(2)==0
J=1+q**6;h0=q**3/(54*J**2);r=h*h-4
t=-b1/a1;tl=-b1l/a1+b1*a1l/a1**2
F=s.cancel(-(t**3+a0*t+b0)/2)
Fl=s.cancel(-((3*t*t+a0)*tl+a0l*t+b0l)/2)
rat=s.factor(s.cancel((F/r).subs(h,h0)))
jet=s.factor(s.cancel((Fl/r).subs(h,h0)))
N,D=s.fraction(rat);G=s.factor_list(N)[1][0][0]
# The rational square numerator is G^2 times a constant.
assert s.degree(G,q)==24
R0=G/(17006112*J**4)
assert s.cancel(rat+2*R0**2)==0
R0l=s.factor(s.cancel(-jet/(4*R0)))
assert s.cancel(jet+4*R0*R0l)==0
branch=11664*J**4-q**6
assert s.gcd(branch,s.diff(branch,q))==1
jetN,jetD=s.fraction(jet)
out={'boundary_F_over_r':str(rat),'derivative_F_over_r':str(jet),'square_numerator':str(G),'jet_numerator_gcd_square':str(s.factor(s.gcd(G,jetN))),'gcd_degree':s.degree(s.gcd(G,jetN),q),'b2_lambda':0,'rational_square_root_factor':str(R0),'lambda_derivative_root_factor':str(R0l),'physical_character_curve':'xi^2=11664*(1+q^6)^4-q^6','curve_genus':11,'scope':'Actual lambda jet on intrinsic boundary; no global Gysin extension asserted'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2,default=str)+'\n');print(json.dumps(out,indent=2,default=str))
