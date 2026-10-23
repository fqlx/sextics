from pathlib import Path
import pickle,sympy as s,json
p=pickle.load(open('/workspace/research/round7/moving_j1728/physical_model.pickle','rb'))
q=p['symbols']['q'];h=p['symbols']['h'];a1,a0,b2,b1,b0=[p['coefficients'][x]for x in ('a1','a0','b2','b1','b0')]
J=1+q**6
h0=q**3/(54*J**2)
t0=s.cancel(-b1/a1)
Fc=s.factor(s.cancel(-(t0**3+a0*t0+b0)/2).subs(h,h0))
Fc=s.factor(s.cancel(Fc))
print('w^3 boundary=',Fc)
N,D=s.fraction(Fc)
out={'component_h':str(h0),'boundary_t':str(s.factor(s.cancel(t0.subs(h,h0)))),'w_cubed':str(Fc),'numerator_factors':[(str(x),int(m))for x,m in s.factor_list(N)[1]],'denominator_factors':[(str(x),int(m))for x,m in s.factor_list(D)[1]],'scope':'Boundary of intrinsic twist surface, not global irregularity or serving proof'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
