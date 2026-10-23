#!/usr/bin/env python3
"""Full generic nine-class affine e-connection by a source-compatible finite matrix."""
import json,time
from pathlib import Path
import sympy as s
from affine_theta_reduction import a,b,q,c,d,e,red,delta,words,mono,vector,J

BASIS=[s.S.One,q,q*q,q**3,q**4,a,a*q,b,b*q]
ROWS=words(20)
# J spans the sole constant primitive kernel; b² coefficient of J is -4.
F_WORDS=[w for w in words(10) if w!=(0,2,0)]
F=[mono(w) for w in F_WORDS]
DJ=delta(J)

def numerator(N,p=e):
    Qp={c:q*q,d:a*q,e:q}[p]
    Jp=a*q if p==d else 0
    return red(s.diff(N,p)*J**2+Qp*(-a*s.diff(N,a)+b*s.diff(N,b))*J-N*Jp*J+N*Qp*(4*a*a+d*a*q+4*b*b))

def matrix():
    fcols=[red(J*delta(f)-f*DJ) for f in F]
    bcols=[red(N*J**2) for N in BASIS]
    M=s.Matrix.hstack(*(vector(x,ROWS) for x in fcols+bcols))
    U=s.Matrix.hstack(*(vector(numerator(N),ROWS) for N in BASIS))
    return M,U

def modular_pivots(M,point=(2,3,5),p=1009):
    A=[[int(x.subs(dict(zip((c,d,e),point))))%p for x in M.row(i)] for i in range(M.rows)]
    # Choose independent original rows by transposed column elimination.
    T=[list(x) for x in zip(*A)]
    piv=[];rr=0
    for j in range(len(T[0])):
        k=next((k for k in range(rr,len(T)) if T[k][j]%p),None)
        if k is None:continue
        T[rr],T[k]=T[k],T[rr]
        iv=pow(T[rr][j],-1,p)
        T[rr]=[(v*iv)%p for v in T[rr]]
        for k in range(len(T)):
            if k!=rr:
                z=T[k][j]
                if z:T[k]=[(v-z*u)%p for v,u in zip(T[k],T[rr])]
        piv.append(j);rr+=1
        if rr==len(T):break
    return piv

def main():
    t=time.monotonic();M,U=matrix();print('built',M.shape,U.shape,round(time.monotonic()-t,2),flush=True)
    piv=modular_pivots(M);print('rank',len(piv),'rows',piv,flush=True)
    assert len(piv)==25
    A=M[piv,:];R=U[piv,:]
    spec={c:2,d:3,e:5}
    As=A.subs(spec);Us=R.subs(spec);Ms=M.subs(spec)
    Cs=As.inv()*Us
    residual=Ms*Cs-U.subs(spec)
    assert residual==s.zeros(37,9)
    print('rational point verifies all333 cleared identities',flush=True)
    data={
      'status':'Exact generic e-connection matrix presentation; source not integrated',
      'equation':'partial_e (N dq/J) = sum_j Gamma_e[j,N] basis_j dq/J + d_q(f_N/J)',
      'curve':{'ab':'q^3','Q':'a^2+b^2+c*q^2+d*a*q+e*q+1','J':str(J)},
      'basis':[str(x) for x in BASIS],
      'f_words':[str(x) for x in F],
      'rows':[str(mono(w)) for w in ROWS],
      'selected_rows':piv,
      'matrix_shape':list(M.shape),
      'generic_rational_formula':'C=A^-1 U_selected; exact primitive coefficients are C[0:16,:], Gamma_e=C[16:25,:]',
      'matrix':[[str(x) for x in M.row(i)] for i in range(M.rows)],
      'e_numerators':[[str(x) for x in U.row(i)] for i in range(U.rows)],
      'point':{'c':2,'d':3,'e':5},
      'rational_point_all_cleared_identities':True,
      'rational_point_gamma_e':[[str(x) for x in Cs[16:25,:].row(i)] for i in range(9)],
    }
    out=Path(__file__).with_name('affine-e-connection-results.json');out.write_text(json.dumps(data,indent=2)+'\n')
    print('saved',out,flush=True)
    print('generic determinant start',flush=True)
    det=s.factor(A.det(method='domain-ge'))
    data['selected_matrix_determinant']=str(det)
    out.write_text(json.dumps(data,indent=2)+'\n')
    print('det',det,flush=True)
if __name__=='__main__':main()
