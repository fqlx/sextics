from pathlib import Path
import pickle,sympy as S,json
HERE=Path(__file__).parent
source=(HERE/'boundary_connection.py').read_text().split('DM=DomainMatrix.from_Matrix(AA)')[0]
exec(compile(source,'boundary_connection_build','exec'))
def payload(f):
 n,d=S.fraction(S.cancel(f));return{'num':{tuple(map(int,e)):str(c)for e,c in S.Poly(n,*pars).as_dict().items()},'den':{tuple(map(int,e)):str(c)for e,c in S.Poly(d,*pars).as_dict().items()}}
rhs={}
for name,parameter in zip(['L','r','x','s'],pars):
 rhs[name]=[]
 for n in sig:
  src=n*h*h*C if name=='s' else -n*S.diff(C,parameter)*D
  rr=S.Matrix([S.Poly(S.expand(x*src),*vv).coeff_monomial(mon(e))for e in rows])
  rhs[name].append([payload(v)for v in rr])
packet={'variables':tuple(map(str,pars)),'A':[[payload(A[i,j])for j in range(A.cols)]for i in range(A.rows)],'RHS':rhs,'column_pivots':piv,'row_pivots':rowpiv,'basis_columns':5,'Q_labels':labs,'rows':rows,'matrix_meaning':'x times common-D²C² coefficient matrix. Solve selected17row/17colminor; scatter to21cols, first5areconnection, last16primitive coefficients. Check all19rows. Derivatives use d(answer)=Ainv*(dRHS-dA*answer), including moving s.'}
(HERE/'boundary_linear_packet.pickle').write_bytes(pickle.dumps(packet))
print('EXPORTED',flush=True)
