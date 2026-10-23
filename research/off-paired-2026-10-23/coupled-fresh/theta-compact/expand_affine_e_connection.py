#!/usr/bin/env python3
import json,time
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix
from affine_e_connection import matrix,c,d,e
p=Path(__file__).with_name('affine-e-connection-results.json')
data=json.loads(p.read_text());M,U=matrix();piv=data['selected_rows'];A=M[piv,:];R=U[piv,:]
t=time.monotonic();print('generic fraction-free solve starts',flush=True)
AA=DomainMatrix.from_Matrix(A).convert_to(s.QQ.poly_ring(c,d,e));RR=DomainMatrix.from_Matrix(R).convert_to(AA.domain)
X,den=AA.solve_den(RR,method='rref')
print('generic solve complete',round(time.monotonic()-t,2),flush=True)
# Verify ALL 333 cleared polynomial coefficients, not merely selected rows.
MM=DomainMatrix.from_Matrix(M).convert_to(AA.domain);UU=DomainMatrix.from_Matrix(U).convert_to(AA.domain)
check=MM.matmul(X)-UU.scalarmul(den)
assert check.is_zero_matrix
print('all333 generic polynomial identities pass',flush=True)
Xm=X.to_Matrix();dd=AA.domain.to_sympy(den)
common=s.gcd_list(list(Xm)+[dd]);Xm=Xm.applyfunc(lambda x:s.div(x,common,c,d,e)[0]);dd=s.div(dd,common,c,d,e)[0]
data['generic_common_denominator']=str(s.factor(dd))
data['generic_primitive_numerators']=[[str(s.factor(x)) for x in Xm[:16,:].row(i)] for i in range(16)]
data['generic_gamma_e_numerators']=[[str(s.factor(x)) for x in Xm[16:25,:].row(i)] for i in range(9)]
data['generic_all_333_cleared_polynomial_identities']=True
data['generic_solve_seconds']=round(time.monotonic()-t,3)
p.write_text(json.dumps(data,indent=2)+'\n')
print('saved',p,'seconds',round(time.monotonic()-t,2),flush=True)
