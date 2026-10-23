from pathlib import Path
import json
import sympy as s
H,C=s.symbols('H C')
I=s.eye(5)
P=s.zeros(5)
for j in range(4): P[j+1,j]=1
P[0,4]=C*H/12
P[1,4]=C**2/12
A=s.zeros(5)
for j in range(5):
 A[:,j]=(3*H*I[:,j]+2*C*P[:,j])/(j+1)
det=s.factor(A.det())
assert s.cancel(det-H*(729*H**4-4*C**6)/360)==0
AI=A.inv().applyfunc(s.cancel)
MH=((I-A.diff(H))*AI).applyfunc(s.factor)
MC=((P-A.diff(C))*AI).applyfunc(s.factor)
assert all(v==0 for v in MH.row(2)) and all(v==0 for v in MC.row(2))
curv=(MC.diff(H)-MH.diff(C)+MH*MC-MC*MH).applyfunc(s.cancel)
assert curv==s.zeros(5)
Euler=(6*H*MH+4*C*MC-s.diag(-4,-2,0,2,4)).applyfunc(s.cancel)
assert Euler==s.zeros(5)
out={'basis':[0,1,2,3,4],'convention':'columns are parameter derivatives of basis elements','A_columns':'v_j=(3H omega_j+2C omega_(j+1))/(j+1), omega5=(CH omega0+C2 omega1)/12','detA':str(det),'MH':[[str(MH[i,j])for j in range(5)]for i in range(5)],'MC':[[str(MC[i,j])for j in range(5)]for i in range(5)],'checks':{'determinant':True,'zero_residue_row':True,'flatness_25_entries':True,'Euler_25_entries':True},'status':'Exact rational connection construction and checks; no current or certificate.'}
Path(__file__).with_name('potential-rank5-connection.json').write_text(json.dumps(out,indent=2))
print('detA =',det)
print('MH tau =',list(MH[:,2]))
print('MC tau =',list(MC[:,2]))
print(json.dumps(out['checks'],indent=2))
