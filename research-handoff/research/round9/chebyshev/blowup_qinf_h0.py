from pathlib import Path
import pickle,sympy as S,json
P=Path(__file__).parent;d=pickle.loads((P/'physical_model.pickle').read_bytes());q,h=d['symbols']['q'],d['symbols']['h'];Q,H,e=S.symbols('Q H e');co={k:S.cancel(v.subs({q:1/Q,h:Q**6*H}))for k,v in d['coefficients'].items()};assert all(S.denom(v).is_Integer for v in co.values())
# Q-chart exceptional coefficients and second point's weighted initial terms.
lead0={k:S.factor(v.subs(Q,0))for k,v in co.items()}
init={}
for k,v in co.items():
 zz=S.Poly(S.expand(v),Q,H);m=min(i+3*j for (i,j),c in zz.terms());init[k]={'weight':m,'initial':S.expand(sum(c*Q**i*H**j for(i,j),c in zz.terms()if i+3*j==m))}
assert init['a1']['initial']==24*H and init['a0']['initial']==-S.Rational(1,243)
assert init['b1']['initial']==-S.Rational(40,27)*H
assert init['b2']['initial']==432*H**2-8*H*Q**3
assert init['b0']['initial']==-S.Rational(2,19683)
# Leading rational exceptional base: parameter T, z=s/H, w=Q^3/H.
T=S.symbols('T');z=S.factor(-(24*T-S.Rational(40,27))/(3*T*T-S.Rational(1,243)));w=S.factor((3*z*z*T+24*z+432)/8)
assert S.cancel(z*(3*T*T-S.Rational(1,243))+24*T-S.Rational(40,27))==0
assert S.cancel(3*z*z*T+24*z+432-8*w)==0
cubic=S.factor(T**3-T/243-S.Rational(2,19683));assert cubic==(27*T-2)*(27*T+1)**2/19683
# The finite order on the Q chart: original normalized algebra, replace last basis e5 by Q6e5.
a=pickle.loads((P/'normalized_algebra.pickle').read_bytes());D=S.diag(1,1,1,1,1,Q**6);bad=[]
for i,M in enumerate(a['matrices']):
 new=(D.inv()*M.subs({q:1/Q,h:Q**6*H},simultaneous=True)*D*(Q**6 if i==5 else 1)).applyfunc(S.cancel)
 for j,v in enumerate(new):
  den=S.denom(v)
  if S.Poly(den,Q,H).total_degree()>0:bad.append((i,j,str(S.factor(den))))
assert not bad
out={'Q_chart':'q=1/Q,h=Q6H; original s=S,t=T,x=X,y=Y unscaled','coefficients':{k:str(v)for k,v in co.items()},'at_Q0':{k:str(v)for k,v in lead0.items()},'second_corner_initial':{k:{'weight':v['weight'],'initial':str(v['initial'])}for k,v in init.items()},'rational_exceptional_base':{'s_over_H':str(z),'Q3_over_H':str(w)},'exceptional_elliptic_surface':{'equation':'y²=x³−27*(27T−2)*(27T+1)²/19683','fibers':'II at T=2/27, IV at T=−1/27, I0* at infinity','pg':0},'finite_order_check':'All transformed multiplication entries polynomial over QQ[Q,H] for basis1,s,s²,(s³+a0s/3)/r,u/r,u²/(H*r³).','scope':'Exact chart, finite algebra, weighted initial terms and rational parametrization. Full strict-transform resolution/adjoint-defect comparison still needs a geometric argument.'}
(P/'blowup_qinf_h0.json').write_text(json.dumps(out,indent=2)+'\n');(P/'blowup_qinf_h0.pickle').write_bytes(pickle.dumps({'Q':Q,'H':H,'coefficients':co,'at_Q0':lead0,'initial':init,'z':z,'w':w}));print(json.dumps({k:v for k,v in out.items()if k!='coefficients'},indent=2))
