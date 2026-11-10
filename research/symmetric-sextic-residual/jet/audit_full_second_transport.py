from pathlib import Path
import sympy as S,json,time
from pathlib import Path
st=time.time();u=S.symbols('u');g=S.Function('g')(u);H=S.Function('H')(u);B0=S.Function('B0')(u);B1=S.Function('B1')(u);G1=S.Function('G1')(u);G2=S.Function('G2')(u);h=H/g;k=-S.diff(g,u)*h*h/(2*g)
assert S.simplify(g*h-H)==0 and S.simplify(g*k+S.diff(g,u)*h*h/2)==0
B1def=G1+h*S.diff(B0,u);physical=G2+h*S.diff(G1,u)+k*S.diff(B0,u)+h*h*S.diff(B0,u,2)/2;reconstructed=G2+h*S.diff(B1def,u)-(h*S.diff(h,u)+S.diff(g,u)*h*h/(2*g))*S.diff(B0,u)-h*h*S.diff(B0,u,2)/2;assert S.simplify(physical-reconstructed)==0
print('PASS formal second-order coordinate/current transport',flush=True)
b,c,d,u,z,ell,K=S.symbols('b c d u z ell K',nonzero=True);loc={str(v):v for v in [b,c,d,u,z,ell,K]};src=json.load(open(Path(__file__).resolve().parent / 'second_source_complete.json'));assert not src['unresolved']
gamma=[S.Integer(0)]*3
for row in src['radials']:
 r,s=row['b_power'],row['d_power'];A=S.sympify(row['A'],locals=loc);gamma[0]+=b**(r+1)*d**s*A;gamma[2]+=b**r*d**(s+1)*A
for row in src['residual_currents']:
 v=[S.sympify(a,locals=loc) for a in row['beta']];factor=S.sympify(row['coefficient'],locals=loc) if row['type']=='unit' else S.Integer(1)
 for i in range(3):gamma[i]+=factor*v[i]
sub={ell:2*(1+z**3),K:2*(1+c**6)};gamma=[v.subs(sub,simultaneous=True) for v in gamma];out=json.load(open(Path(__file__).resolve().parent / 'relative_second_complete.json'));first=json.load(open(Path(__file__).resolve().parent / 'relative_first_complete.json'));assert out['beta0']==first['beta0'] and out['beta1']==first['beta1']
for i in range(3):
 actual=S.sympify(out['normal_gamma2'][i],locals=loc)
 if actual!=gamma[i]: assert S.cancel(actual-gamma[i])==0,('gamma mismatch',i)
print('PASS all 22 radial +35 residual terms assembled into stored gamma2',round(time.time()-st,1),flush=True)
B0=[S.sympify(v,locals=loc) for v in first['beta0']];B1=[S.sympify(v,locals=loc) for v in first['beta1']];q=1+2*b-u;r=c*c+2*c*d-z*u;HH=6*(1+z*c**4)*u+6*(1+z*z*c*c)*u*u+(q*q*r+2*q*r*r)/7;gg=6*(1+z**3)*u*u;h=HH/gg;corr=h*S.diff(h,u)+S.diff(gg,u)*h*h/(2*gg)
for i in range(3):
 expected=gamma[i]+h*S.diff(B1[i],u)-corr*S.diff(B0[i],u)-h*h*S.diff(B0[i],u,2)/2;actual=S.sympify(out['beta2'][i],locals=loc)

 if actual!=expected: assert S.cancel(actual-expected)==0,('beta2 mismatch',i)
print('PASS all stored beta2 components and protected parameter specialization',round(time.time()-st,1),flush=True)
