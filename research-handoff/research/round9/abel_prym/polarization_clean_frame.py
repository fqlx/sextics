"""Transport the independently audited pairing to the literal clean eta frame."""
import sympy as s,pickle,json,time
from pathlib import Path
from sympy.polys.fields import field
from sympy.polys.domains import QQ
HERE=Path(__file__).parent;start=time.monotonic()
p=pickle.load(open(HERE/'polarization.pickle','rb'));g=pickle.load(open(HERE.parent/'cyclic_full'/'global_eta_complete.pickle','rb'))
W,h,t,L,r,x=p['symbols'];F,fl,fr,fx=field('L,r,x',QQ)
H=[[F.from_expr(p['pairing_actual_rows_conjugate_columns'][i,j])for j in range(3)]for i in range(3)]
loc={'L':L,'r':r,'x':x}
def expr(v):return s.sympify(v['numerator'].replace('^','**'),locals=loc)/s.sympify(v['denominator'].replace('^','**'),locals=loc)
P=[[F.from_expr(expr(v))for v in row]for row in g['P']]
HH=[[sum(P[i][k]*H[k][j]for k in range(3))for j in range(3)]for i in range(3)]
HH=s.Matrix([[v.as_expr()for v in row]for row in HH]);P=s.Matrix([[v.as_expr()for v in row]for row in P])
p.update({'pairing_actual_rows_conjugate_columns':HH,'actual_frame':'global_eta_complete literal polynomial eta_new','cohomology_gauge_from_old':P,'conjugate_frame':'conjugate_fast unchanged','normalization':p['normalization'],'transport':'H_clean=P*H_old, since beta_clean=P*beta_old in cohomology. Exact P gauge and proper connections were independently verified in the source packets.'})
(HERE/'polarization_clean_frame.pickle').write_bytes(pickle.dumps(p))
result={'frame':p['actual_frame'],'conjugate_frame':p['conjugate_frame'],'transport':'H_clean=P*H_old','matrix_terms':[[len(s.Poly(s.fraction(z)[0],L,r,x).terms())for z in row]for row in HH.tolist()],'seconds':time.monotonic()-start,'scope':'Exact rational gauge transport of the audited flat pairing; common topological scalar remains unspecified.'}
(HERE/'polarization_clean_frame.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
