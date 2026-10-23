from pathlib import Path
import pickle,sympy as S,json
P=Path(__file__).parent;d=pickle.loads((P/'physical_model.pickle').read_bytes());q,h,s,t=[d['symbols'][x]for x in('q','h','s','t')];a1,a0,b2,b1,b0=S.symbols('a1 a0 b2 b1 b0');j1,j0,l2,l1,l0=S.symbols('a1l a0l b2l b1l b0l')
D=(6*s*t+a1)**2-3*s*s*(3*t*t+a0+9*s*s)
sl=(-(6*s*t+a1)*(j1*s+l2)+3*s*s*(j1*t+j0*s+l1))/D
tl=((3*t*t+a0+9*s*s)*(j1*s+l2)-(6*s*t+a1)*(j1*t+j0*s+l1))/D
assert S.cancel((6*s*t+a1)*sl+3*s*s*tl+j1*s+l2)==0
assert S.cancel((3*t*t+a0+9*s*s)*sl+(6*s*t+a1)*tl+j1*t+j0*s+l1)==0
c0=t**3+a0*t+b0;c0l=(3*t*t+a0)*tl+j0*t+l0
# Witness in irreducible degree6 extension at p173,q2,h14.
p=173;point={q:2,h:14};md=lambda v:int(S.Rational(v).p)%p*pow(int(S.Rational(v).q)%p,-1,p)%p
co={x:md(d['coefficients'][str(x)].subs(point))for x in(a1,a0,b2,b1,b0)}
je={z:md(d['jets'][str(x)].subs(point))for x,z in zip((a1,a0,b2,b1,b0),(j1,j0,l2,l1,l0))}
pp=S.Poly(d['P'].subs(point),s);f=S.Poly(sum(md(pp.nth(i))*s**i for i in range(7)),s,modulus=p).monic()
def red(expr):
 n,de=S.cancel(expr).as_numer_denom();N=S.Poly(n,s,modulus=p);DD=S.Poly(de,s,modulus=p);return (N*S.invert(DD,f)).rem(f).as_expr()
t0=red(-(co[a1]*s+co[b2])/(3*s*s));subs=co|je|{t:t0}
slv=red(sl.subs(subs));tlv=red(tl.subs(subs));cv=red(c0.subs(subs));clv=red(c0l.subs(subs));tauv=red(-cv/s**3);taul=red(-clv/s**3+3*cv*slv/s**4)
# Elliptic coefficient jet and j derivative are an actual-source projection witness.
Av=red(-27*s*s);Bv=red(-27*cv);Al=red(-54*s*slv);Bl=red(-27*clv)
jv=red(1728*4*Av**3/(4*Av**3+27*Bv**2));jl=red(jv*(3*Al/Av-(12*Av**2*Al+54*Bv*Bl)/(4*Av**3+27*Bv**2)))
assert slv!=0 and taul!=0 and jl!=0
out={'formulas':{'Jacobian_det':str(D),'s_lambda':str(sl),'t_lambda':str(tl),'c0_lambda':str(c0l),'E2_A_lambda':'−54*s*s_lambda','E2_B_lambda':'−27*c0_lambda'},'actual_jets':{str(x):str(v)for x,v in d['jets'].items()},'witness':{'prime':p,'q':2,'h':14,'irreducible_slope_modulus':str(f.as_expr()),'s_lambda':str(slv),'tau_lambda':str(taul),'E2_j_lambda':str(jl)},'scope':'Actual λA deformation, not arbitrary family tangent. Nonzero quotient deformation is not by itself a Gysin certificate.'}
(P/'source_jet.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
