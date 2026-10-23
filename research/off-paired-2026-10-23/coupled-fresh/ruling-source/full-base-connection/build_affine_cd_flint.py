"""Two additional literal generic base connections, with native exact solves.

Reuses the complete 37x25 reduction chart from theta-compact, but builds
the c,d right sides afresh.  Every one of the 666 cleared polynomial
identities is verified, including all sixteen rational fiber primitives.
"""
import hashlib,json,sys,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq

HERE=Path(__file__).resolve().parent
THETA=HERE.parents[1]/'theta-compact'
sys.path.insert(0,str(THETA))
from affine_e_connection import matrix,numerator,BASIS,ROWS,F,c,d,e,red,vector

ctx=fmpq_mpoly_ctx.get(('c','d','e'))
zero=ctx.constant(0)
def conv(x):return ctx.from_dict({k:fmpq(str(v)) for k,v in s.Poly(x,c,d,e).terms()})

def main():
    started=time.monotonic()
    chart=json.loads((THETA/'affine-e-connection-results.json').read_text())
    checkpoint=json.loads((THETA/'core-checkpoint-V.json').read_text())
    M,_=matrix()
    U=s.Matrix.hstack(*(vector(numerator(N,p),ROWS) for p in (c,d) for N in BASIS))
    MM=[[conv(x)for x in M.row(r)]for r in range(M.rows)]
    UU=[[conv(x)for x in U.row(r)]for r in range(U.rows)]
    selected=chart['selected_rows']
    A=[[MM[r][k]for k in range(25)]for r in selected]
    R=[[UU[r][j]for j in range(18)]for r in selected]
    rr=list(range(25));cc=list(range(25))
    for r,k in checkpoint['pivot_pairs']:
        z=A[r][k]
        assert set(z.to_dict())=={(0,0,0)}
        for v in cc:A[r][v]=A[r][v]//z
        for j in range(18):R[r][j]=R[r][j]//z
        rr.remove(r);cc.remove(k)
        for x in range(25):
            if x==r:continue
            z=A[x][k]
            if not z:continue
            for v in cc:A[x][v]-=z*A[r][v]
            for j in range(18):R[x][j]-=z*R[r][j]
            A[x][k]=zero
    assert rr==checkpoint['rows'] and cc==checkpoint['cols']
    n=len(rr);m=18
    print('same unit pivots; native core',n,'rhs',m,flush=True)
    Z=[[A[r][k]for k in cc]+R[r][:]for r in rr]
    prev=ctx.constant(1)
    for k in range(n):
        if not Z[k][k]:
            r=next(r for r in range(k+1,n)if Z[r][k]);Z[k],Z[r]=Z[r],Z[k]
        pivot=Z[k][k]
        for x in range(n):
            if x==k:continue
            z=Z[x][k]
            for j in range(n+m):
                if j==k:continue
                quo,rem=divmod(pivot*Z[x][j]-z*Z[k][j],prev)
                assert not rem,(k,x,j)
                Z[x][j]=quo
            Z[x][k]=zero
        prev=pivot
        print('core pivot',k+1,flush=True)
    den=Z[0][0]
    assert all(Z[x][x]==den for x in range(n))
    vals=[Z[x][n+j]for x in range(n)for j in range(m)]
    common=den
    for z in vals:
        common=common.gcd(z)
        if common==1:break
    den=den//common
    vals=[z//common for z in vals]
    Y=[[zero for _ in range(m)]for _ in range(25)]
    for x,k in enumerate(cc):
        for j in range(m):Y[k][j]=vals[x*m+j]
    for r,k in checkpoint['pivot_pairs']:
        for j in range(m):Y[k][j]=R[r][j]*den-sum((A[r][v]*Y[v][j]for v in cc),zero)
    # A single global common factor is harmless and improves the descended
    # exact arrays.  No individual entry is converted back through SymPy.
    common=den
    for ar in Y:
        for z in ar:
            common=common.gcd(z)
            if common==1:break
        if common==1:break
    den=den//common;Y=[[z//common for z in ar]for ar in Y]
    source=(THETA/'affine_e_connection.py').read_bytes()
    result={
        'status':'Exact generic c,d compact/open connections with literal fiber primitives; source still open',
        'coefficient_field':'Q(c,d,e)',
        'directions':['partial_c','partial_d'],
        'basis':[str(x)for x in BASIS],
        'primitive_words':[str(x)for x in F],
        'primitive_denominator':'J; each primitive is sum(coeff_word*word)/J',
        'convention':'partial_p basis_j=sum_i Gamma_p[i,j]*basis_i+d_q(primitive_p[j]); basis forms include dq/J',
        'common_denominator':str(den),
        'gamma_numerators':{
            name:[[str(Y[16+r][off+j])for j in range(9)]for r in range(9)]
            for name,off in [('c',0),('d',9)]},
        'primitive_numerators':{
            name:[[str(Y[r][off+j])for j in range(9)]for r in range(16)]
            for name,off in [('c',0),('d',9)]},
        'source_matrix_sha256':hashlib.sha256(source).hexdigest(),
        'reused_core_dimension':n,
        'all_666_generic_cleared_polynomial_identities':False,
        'certificate':False,
    }
    out=HERE/'affine-cd-generic-results.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('arrays checkpointed before complete audit',round(time.monotonic()-started,2),flush=True)
    for r in range(37):
        for j in range(18):
            assert sum((MM[r][k]*Y[k][j]for k in range(25)),zero)==UU[r][j]*den,(r,j)
    result['all_666_generic_cleared_polynomial_identities']=True
    result['seconds']=round(time.monotonic()-started,3)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('all666 literal generic polynomial identities pass',result['seconds'],flush=True)

if __name__=='__main__':main()
