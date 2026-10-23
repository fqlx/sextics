#!/usr/bin/env python3
"""Unit-pivot elimination before exact small-core generic GM solve."""
import json,time,sys
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix
from affine_e_connection import matrix,numerator,BASIS,ROWS,F,c,d,e,a,b,q,J,red,vector

def flint_solve(A,B):
    from flint import fmpq_mpoly_ctx, fmpq
    ctx=fmpq_mpoly_ctx.get(('c','d','e'))
    def conv(x):
        return ctx.from_dict({k:fmpq(str(v)) for k,v in s.Poly(x,c,d,e).terms()})
    n=A.rows;m=B.cols
    Z=[[conv(A[i,j]) for j in range(n)]+[conv(B[i,j]) for j in range(m)] for i in range(n)]
    prev=ctx.constant(1)
    for k in range(n):
        if not Z[k][k]:
            r=next(r for r in range(k+1,n) if Z[r][k]);Z[k],Z[r]=Z[r],Z[k]
        pivot=Z[k][k]
        for i in range(n):
            if i==k:continue
            z=Z[i][k]
            for j in range(n+m):
                if j==k:continue
                val=pivot*Z[i][j]-z*Z[k][j]
                quo,rem=divmod(val,prev)
                assert not rem,(k,i,j)
                Z[i][j]=quo
            Z[i][k]=ctx.constant(0)
        prev=pivot
        print('FLINT Bareiss pivot',k+1,flush=True)
    den=Z[0][0]
    assert all(Z[i][i]==den for i in range(n))
    vals=[Z[i][n+j] for i in range(n) for j in range(m)]
    common=den
    for val in vals:
        common=common.gcd(val)
        if common==1:break
    den=den//common;vals=[x//common for x in vals]
    def sym(x):return s.Poly.from_dict({k:s.Rational(str(v)) for k,v in x.to_dict().items()},(c,d,e)).as_expr()
    return s.Matrix(n,m,[sym(x) for x in vals]),sym(den)

def solve_units(A,R):
    A=A.copy();R=R.copy();n=A.rows
    rr=list(range(n));cc=list(range(n));pivs=[]
    while rr:
        hit=next(((r,k) for r in rr for k in cc if A[r,k].is_Rational and A[r,k]!=0),None)
        if hit is None:break
        r,k=hit;z=A[r,k]
        if z!=1:
            for j in cc:A[r,j]=s.expand(A[r,j]/z)
            for j in range(R.cols):R[r,j]=s.expand(R[r,j]/z)
        rr.remove(r);cc.remove(k)
        for x in range(n):
            if x==r:continue
            z=A[x,k]
            if z==0:continue
            for j in cc:A[x,j]=s.expand(A[x,j]-z*A[r,j])
            for j in range(R.cols):R[x,j]=s.expand(R[x,j]-z*R[r,j])
            A[x,k]=s.S.Zero
        pivs.append((r,k))
        print('unit pivots',len(pivs),'core',len(rr),flush=True)
    if rr:
        core_checkpoint={"A":[[str(x) for x in A[rr,cc].row(i)] for i in range(len(rr))],"B":[[str(x) for x in R[rr,:].row(i)] for i in range(len(rr))],"rows":rr,"cols":cc,"pivot_pairs":pivs,"full_A":[[str(x) for x in A.row(i)] for i in range(n)],"full_B":[[str(x) for x in R.row(i)] for i in range(n)]}
        Path(__file__).with_name('core-checkpoint-'+sys.argv[1]+'.json').write_text(json.dumps(core_checkpoint))
        print('FLINT Bareiss core solve',len(rr),flush=True)
        Xden,den=flint_solve(A[rr,cc],R[rr,:])
    else:Xden=s.zeros(0,R.cols);den=s.S.One
    Y=s.zeros(n,R.cols)
    for ii,k in enumerate(cc):
        for j in range(R.cols):Y[k,j]=Xden[ii,j]
    for r,k in pivs:
        for j in range(R.cols):Y[k,j]=s.expand(R[r,j]*den-sum(A[r,v]*Y[v,j] for v in cc))
    return Y,den,len(rr)

def main():
    mode=sys.argv[1] if len(sys.argv)>1 else 'e'
    p=Path(__file__).with_name('affine-e-connection-results.json');data=json.loads(p.read_text())
    M,U=matrix();piv=data['selected_rows'];A=M[piv,:]
    if mode=='V':
        U=s.Matrix.hstack(*(vector(red(2*c*numerator(N,c)+d*numerator(N,d)+e*numerator(N,e)),ROWS) for N in BASIS))
    R=U[piv,:];t=time.monotonic();X,den,ncore=solve_units(A,R)
    print('solve seconds',round(time.monotonic()-t,2),'core',ncore,flush=True)
    check=M*X-U*den
    assert all(s.expand(x)==0 for x in check)
    print('all333 generic polynomial identities pass',flush=True)
    common=s.gcd_list(list(X)+[den]);X=X.applyfunc(lambda x:s.div(x,common,c,d,e)[0]);den=s.div(den,common,c,d,e)[0]
    result={
        'mode':mode,'basis':[str(x) for x in BASIS],'f_words':[str(x) for x in F],
        'common_denominator':str(s.factor(den)),
        'primitive_numerators':[[str(s.factor(x)) for x in X[:16,:].row(i)] for i in range(16)],
        'gamma_numerators':[[str(s.factor(x)) for x in X[16:25,:].row(i)] for i in range(9)],
        'all_333_generic_cleared_polynomial_identities':True,
        'seconds':round(time.monotonic()-t,3),'remaining_core':ncore,
    }
    out=p.with_name('affine-'+mode+'-generic-results.json');out.write_text(json.dumps(result,indent=2)+'\n');print('saved',out,flush=True)
if __name__=='__main__':main()
