from pathlib import Path
import sympy as S,json
P=Path(__file__).parent;B,delta,eta,SS,x,U,V,C=S.symbols('B delta eta SS x U V C')
# delta=q_*^3=+-i, eta=T/S=+-i are independent choices.
b2=(delta*B-54)/(8*B**8)
s3=-(delta*B-54)/(24*eta*B**8)
assert S.cancel(3*eta*s3+b2)==0
B1=54/delta;C0=S.cancel(-54/(24*eta*B1**8))
assert S.cancel(s3.subs(B,B1/x)-C0*x**7*(1-x))==0
# U²=S; V=U/x, so V6=C0*x(1-x).
# The order3 deck acts U,V byomega and fixesx; quotient is the conic Z²=C0*x(1-x).
out={'weights':'j=epsilon3,z=1/h=epsilon6*B,s=epsilon^-14*S,t=epsilon^-14*T,xE=epsilon^-14*X,yE=epsilon^-21*Y','leading_b2':str(b2),'components':'T=eta*S, eta²=−1; delta=q_*³ also satisfiesdelta²=−1','S_cubed':str(s3),'tau':'eta, hence jE=6912/5','twist_curve':{'U':'U²=S','x':'54/(delta*B)','V':'U/x','equation':'V6=C0*x(1-x)','C0':str(C0),'genus':2},'index3_deck':'epsilon→omegaepsilon; S,X→omega²(S,X), Yfixed; U,V→omega(U,V)','constant_E_coordinates':'X/S and Y/U³ are fixed by index3deck','conclusion':'Reduced leading exceptional Hol2 vanishes after index3trace because curve quotient byV→omegaV is a rational conic. This does not control conormal thickenings/R² or global forms.','remaining':'Determine normal bundle/equivariant conormal layers and their adjoint connecting map; actual λ starts3epsilonweights above leading.'}
(P/'J_corner_leading.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
