from pathlib import Path
from collections import defaultdict
import sympy as S,pickle,json
P=Path(__file__).parent;packet=pickle.load(open('/workspace/research/round9/abel_prym/effective_graph.pickle','rb'));z,E,B,R,k,g=S.symbols('zeta E B R k gamma');coeff=defaultdict(lambda:0)
# physical chart X0=k6 gamma3E,X1=gamma3E,b=k18gamma6B,delta=k30gamma12BR.
for ex,c in packet['D'].items():
 e0,e1,e2,ea,eb,e5=ex
 for j in range(9):
  key=(6*e0+18*eb+30*j,3*(e0+e1)+6*eb+12*j,e0+e1,eb+j,j)
  coeff[key]+=S.Integer(c)*(-1)**j*S.binomial(S.Rational(ea,6),j)*z**ea
nonzero=[]
for (x,y,ee,bb,rr),c in coeff.items():
 c=S.rem(S.Poly(S.expand(c),z),S.Poly(z**6+1,z)).as_expr()
 if c!=0:nonzero.append((x,y,ee,bb,rr,c))
pts=sorted(set((x,y)for x,y,*_ in nonzero));lower=[]
for p in pts:
 while len(lower)>=2:
  a,b=lower[-2:];cross=(b[0]-a[0])*(p[1]-b[1])-(b[1]-a[1])*(p[0]-b[0])
  if cross<=0:lower.pop()
  else:break
 lower.append(p)
# Keep faces whose inward normalhas bothcoordinatespositive.
faces=[]
for a,b in zip(lower,lower[1:]):
 dx=b[0]-a[0];dy=b[1]-a[1]
 if dx>0 and dy<0:
  wx,wy=-dy,dx;dd=S.igcd(wx,wy);wx//=dd;wy//=dd;val=wx*a[0]+wy*a[1]
  terms=[S.expand(c*E**ee*B**bb*R**rr*k**x*g**y)for x,y,ee,bb,rr,c in nonzero if wx*x+wy*y==val]
  face=S.factor(sum(terms));faces.append({'a':a,'b':b,'normal':[int(wx),int(wy)],'value':int(val),'support_count':len(terms),'polynomial':str(face)})
# Fixed slope5 face in nonfactor chart at physicalweights X0=7,X1=X2=5,b16,delta30.
wx,wy=1,5;val=min(wx*x+wy*y for x,y,*_ in nonzero);terms=[c*E**ee*B**bb*R**rr*k**x*g**y for x,y,ee,bb,rr,c in nonzero if wx*x+wy*y==val];ff=S.factor(sum(terms));out={'substitution':'X0=k6 gamma3E,X1=gamma3E,Y1=k18gamma6B,delta=k30gamma12BR','delta_series_order':8,'point_count':len(pts),'positive_lower_faces':faces,'slope5_minimum':int(val),'slope5_face':str(ff),'global_min_gamma':min(y for x,y in pts),'global_min_k':min(x for x,y in pts),'scope':'Exact coefficient cancellations modulo zeta6+1; finite delta truncation8 contains all lowerpositiveNewtonfaces becausehigherj adds(30,12).'};(P/'vertex_newton.json').write_text(json.dumps(out,indent=2)+'\n');(P/'vertex_newton.pickle').write_bytes(pickle.dumps({'symbols':{'zeta':z,'E':E,'B':B,'R':R,'k':k,'gamma':g},'terms':nonzero,'faces':faces,'slope5':ff}));print(json.dumps(out,indent=2))
