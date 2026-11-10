from pathlib import Path
import json,sympy as S,time
from pathlib import Path
st=time.time();x,u=S.symbols('x u');F=S.Function('F')(x,u);H=S.Function('H')(x,u);V=S.Function('V')(x,u);g=S.diff(F,u);v=H/g;D=lambda w:S.diff(w,x)-S.diff(F,x)/g*S.diff(w,u);vary=(-S.diff(H,x)/g+S.diff(F,x)*S.diff(H,u)/g**2)*S.diff(V,u);assert S.simplify(D(v*S.diff(V,u))+vary-v*S.diff(D(V),u))==0
P=S.Function('P')(u);gg=S.Function('g')(u);hh=S.Function('H')(u);S0=2*(gg*S.diff(P,u)-S.diff(gg,u)*P)/gg**3;S1=2*((S.diff(hh,u)*S.diff(P,u)-S.diff(hh,u,2)*P)/gg**3-3*S.diff(hh,u)*(gg*S.diff(P,u)-S.diff(gg,u)*P)/gg**4);pv=-S.diff(hh*P/gg,u);assert S.simplify(S1-hh/gg*S.diff(S0,u)-2/gg*S.diff(pv/gg,u))==0
print('PASS universal moving-fiber source and current transport',flush=True)
B,D,U,L,K,p0,p1,p2,aa,bb=S.symbols('B D U L K p0 p1 p2 aa bb');FF=B**3+D**3+L*U**3+K;gg0=3*L*U**2;pp=p0+p1*U+p2*U**2;hd=3*L*(aa*U+bb*U**2);g1=S.diff(hd,U);zb=B*(2*D**3+K)/(2*U*(D**3+K));zd=D*(2*B**3+K)/(2*U*(B**3+K));c2=p0/(9*L*K);c1=p1/(9*L*K);wb=B*(c2/U**2+c1/U)-c1*zb;wd=D*(c2/U**2+c1/U)-c1*zd
c4=aa*p0/(9*L*K);C2=-(aa*p2+bb*p1)/(9*L*K);C1=-2*bb*p2/(9*L*K)-2*aa*p0/(9*K*K);wb1=(aa/U+bb)*S.diff(wb,U)+B*(c4/U**4+C2/U**2+C1/U)-C1*zb;wd1=(aa/U+bb)*S.diff(wd,U)+D*(c4/U**4+C2/U**2+C1/U)-C1*zd
T0=lambda w,j:S.diff(w,j)-S.diff(FF,j)*S.diff(w,U)/gg0
source0=(gg0*S.diff(pp,U)-S.diff(gg0,U)*pp)/gg0**3;source1=(g1*S.diff(pp,U)-S.diff(g1,U)*pp)/gg0**3-3*g1*(gg0*S.diff(pp,U)-S.diff(gg0,U)*pp)/gg0**4;dv=sum((-S.diff(hd,j)/gg0+S.diff(FF,j)*g1/gg0**2)*S.diff(w,U) for j,w in [(B,wb),(D,wd)]);err=source1-dv-hd/gg0*S.diff(source0-T0(wb,B)-T0(wd,D),U)-T0(wb1,B)-T0(wd1,D);num=S.fraction(S.cancel(err))[0];assert S.rem(num,FF,D)==0
print('PASS arbitrary diagonal first lift by literal rational reduction',flush=True)
b,c,d,u,z,ell,K=S.symbols('b c d u z ell K');baseb=2*d*(-(c*c+z)*b*b/(36*ell*u*(d**6+K))+c*c*b*b/(18*ell*K*u*u));based=2*b*(-(c*c+z)*d*d/(36*ell*u*(b**6+K))+c*c*d*d/(18*ell*K*u*u));qm=1+2*b-u;rm=c*c+2*c*d-z*u;hm=(qm*qm*rm+2*qm*rm*rm)/7;gbase=3*ell*u*u
sub={B:b*b,D:d*d,U:u,L:ell,p0:c*c,p1:-(c*c+z),p2:z,aa:2*(1+z*c**4)/ell,bb:2*(1+z*z*c*c)/ell};diagb=d*wb1.subs(sub,simultaneous=True);diagd=b*wd1.subs(sub,simultaneous=True)
loc={str(q):q for q in (b,c,d,u,z,ell,K)};M=json.load(open(Path(__file__).resolve().parent / 'mixed-first-complete.json'));mixedb=S.sympify(M['beta_b'],locals=loc);mixedd=S.sympify(M['beta_d'],locals=loc);phys=[diagb+hm/gbase*S.diff(baseb,u)+mixedb,diagd+hm/gbase*S.diff(based,u)+mixedd];subs={ell:2*(1+z**3),K:2*(1+c**6)};Pj=json.load(open(Path(__file__).resolve().parent / 'relative_first_complete.json'))
for i,j in enumerate((0,2)):
 expected=phys[i].subs(subs,simultaneous=True);actual=S.sympify(Pj['beta1'][j],locals=loc)

 if actual!=expected:
  print('mismatch',j,'actual addends',len(S.Add.make_args(actual)),'expected addends',len(S.Add.make_args(expected)),'numeric', (actual-expected).subs({b:2,c:3,d:4,u:5,z:6}),flush=True)
  print('cancel starting',flush=True);diff=S.cancel(actual-expected);print('cancel result',str(diff)[:500],flush=True);assert diff==0
 actual0=S.sympify(Pj['beta0'][j],locals=loc);assert actual0==[baseb,based][i].subs(subs,simultaneous=True)
assert Pj['beta0'][1]=='0' and Pj['beta1'][1]=='0'
print('PASS stored physical beta0/beta1 exact assembly, protected ell/K specialization',round(time.time()-st,2),flush=True)
