"""Complete good-frame primitives, verifying all higher lifts independently."""
from pathlib import Path
import sympy as s,pickle,json,time,importlib.util
root=Path(__file__).parent;start=time.monotonic()
spec=importlib.util.spec_from_file_location('native_rf_complete',root/'theta_frame.py');rf=importlib.util.module_from_spec(spec);spec.loader.exec_module(rf)
raw=pickle.loads((root/'actual_fast.pickle').read_bytes());data=pickle.loads((root/'global_eta_frame.pickle').read_bytes());high=pickle.loads((root/'global_eta_high_input.pickle').read_bytes())
W,h,t,L,r,x=raw['symbols'];vv=(W,h,t);C=raw['curve'];E=data['new_numerator'];mons=data['monomials'];lab8=data['lab8'];lab14=high['labs']
parse=lambda d:rf.RF(rf.fmpq_mpoly(d['numerator'],rf.ctx),rf.fmpq_mpoly(d['denominator'],rf.ctx))
T=[[parse(z)for z in row]for row in data['lower_Jacobian_inverse']]
N={n:[[parse(z)for z in row]for row in mat]for n,mat in data['connection'].items()}
mon=lambda e:W**e[0]*h**e[1]*t**e[2]
div=s.Matrix([[s.Poly(s.diff(mon(e),vv[i]),*vv).coeff_monomial(z)for i,e in lab8]for z in (h*h,t)])
text=(root/'global_eta_high.log').read_text();assert '\nPOWER\n0\n' in text and '\nCOEFF 2 36\n' in text and '?'not in text
out={};denfacts={}
for j,(name,par)in enumerate(zip(('L','r','x'),(L,r,x))):
    coefficients=[s.sympify(text.split('COEFF '+str(j)+' '+str(i)+'\n')[1].split('\n')[0].replace('^','**'))/x for i in range(1,37)]
    Q14=[s.factor(sum(c*mon(e)for c,(i,e)in zip(coefficients,lab14)if i==k))for k in range(3)]
    lift_error=E*s.diff(C,par)-sum(Q*s.diff(C,v)for Q,v in zip(Q14,vv))
    assert s.expand(s.cancel(x*x*lift_error))==0
    P8=s.expand(s.diff(E,par)-sum(s.diff(Q,v)for Q,v in zip(Q14,vv)))
    target=[rf.convert(s.Poly(P8,*vv).coeff_monomial(mm))for mm in mons]
    coeff=[sum((T[i][k]*target[k]for k in range(10)),rf.zero)for i in range(10)]
    row=[sum((rf.convert(div[i,k])*coeff[k]for k in range(9)),rf.zero)for i in range(2)]+[coeff[-1]]
    assert all(not(a-b).n for a,b in zip(row,N[name][2]))
    den=rf.ctx.constant(1)
    for v in coeff:
        den=den*v.d//den.gcd(v.d)
    factors=[{'factor':str(f),'exponent':int(e)}for f,e in den.factor()[1]];denfacts[name]=factors
    out[name]=dict(Q14=Q14,Q14_coefficients=coefficients,lab14=lab14,
                   Q8_coefficients=[z.json()for z in coeff[:9]],eta_coefficient=coeff[-1].json(),
                   connection_row=[z.json()for z in row],
                   primitive='i_Q14 Omega/C² - i_Q8 Omega/C',
                   exact_polynomial_lift=True,exact_connection_row=True)
data['eta_primitives']=out;data['eta_lower_denominators']=denfacts;data['complete_primitives']=True
data['primitive_affine_convention']='On h=1, Q_aff=(Q_W-W*Q_h,Q_t-2*t*Q_h); Omega=dW wedge dt; use i_Q_aff Omega.'
data['complete_primitive_scope']='All nine basis derivatives now have exact primitives with only x,D1,D2 poles.'
(root/'global_eta_complete.pickle').write_bytes(pickle.dumps(data))
ans=dict(complete_primitives=True,higher_identity_verified_all_three=True,eta_connection_row_verified_all_three=True,
         Q14_parameter_denominators=['1','1','x'],eta_Q8_parameter_denominators=denfacts,
         new_numerator=str(E),seconds=time.monotonic()-start,
         scope='Complete clean-frame connection and relative primitives, no current or original target certificate.')
(root/'global_eta_complete.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
