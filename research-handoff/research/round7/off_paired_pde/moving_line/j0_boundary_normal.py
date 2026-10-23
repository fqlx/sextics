from pathlib import Path
import pickle,sympy as s,json
P=pickle.load(open('/workspace/research/round7/moving_j1728/legendre_model.pickle','rb'))
q,h=[P['symbols'][x]for x in ('q','h')];ell=s.symbols('ell')
a1,a0,b2,b1,b0=[P['coefficients'][x]for x in ('a1','a0','b2','b1','b0')]
J=1+q**6;h0=q**3/(54*J**2);t=-b1/a1
H1=-a1/s.diff(b2,h)
T1=-((s.diff(a1,h)*t+s.diff(b1,h))*H1+3*t*t+a0)/a1
T3=8*ell/a1
R1=-((s.diff(a0,h)*t+s.diff(b0,h))*H1+(3*t*t+a0)*T1)/(4*ell)
R3=-(3*t*t+a0)*T3/(4*ell)
R1=s.factor(s.cancel(R1).subs(h,h0));R1=s.factor(s.cancel(R1))
R3=s.factor(s.cancel(R3).subs(h,h0));R3=s.factor(s.cancel(R3))
out={'definitions':'s=w*v, boundary w^3=F(q); normal parameter v','w_cubed_v':'R1(q)*w+R3(q)*w^3','R1':str(R1),'R3':str(R3),'R1_zero':R1==0,'scope':'Boundary normal jet; retaining the R1*w term is essential for extension of boundary hol1'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
