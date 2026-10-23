from pathlib import Path
import pickle,sympy as s,json
H=Path(__file__).parent;d=pickle.load(open(H/'strict_normalization.pickle','rb'));a,b,t,v,e=d['variables'];p=d['parts'];out={}
def rem(expr):
 dd={}
 for term in s.Add.make_args(s.expand(expr.subs(t,1))):
  pw=term.as_powers_dict();i=int(pw.get(a,0));j=int(pw.get(v,0));c=s.cancel(term/a**i/v**j)
  assert c.is_Rational
  ij=(i%6,j%6);sg=1 if (i//6+j//6)%2==0 else -1;dd[ij]=dd.get(ij,0)+c*sg
 return s.Poly.from_dict(dd,(a,v)).as_expr()
for k in [13,15]:
 q,r,ss=p[k]
 # S and P can serve as etale coordinates in a and v at the indicated roots.
 names={'qP':s.diff(q,v)/(6*v**5),'rP':s.diff(r,v)/(6*v**5),'sS':s.diff(ss,a)/(6*a**5),'sb':s.diff(ss,b)}
 for n,g in names.items():
  # reduce inverses a^-5=-a,v^-5=-v on the roots
  g=g.subs(b,0).subs(t,1);g=s.cancel(g).subs(a**(-5),-a).subs(v**(-5),-v)
  out[f'{k}_{n}']=str(s.factor(rem(s.cancel(g))))
(H/'special_P_coefficients.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
