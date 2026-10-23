"""Recover the literal fixed-x primitive for the existing V connection.

V=e*d/de=6v*d/dv at fixed i,j.  Deck descent also changes x=e*q;
the exact Cartan primitive -contraction_(x*d/dx)(nu) is mandatory.
The compact connection matrices agree with theta's existing V result.
"""
import hashlib,json,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly
from descend_ij_connections_flint import C,T,ii,jj,vv,zero,one,weights,descend,matmul,add

HERE=Path(__file__).resolve().parent
THETA=HERE.parents[1]/'theta-compact'

def main():
    started=time.monotonic()
    src=THETA/'affine-V-generic-results.json'
    raw=json.loads(src.read_text())
    assert raw['all_333_generic_cleared_polynomial_identities']
    den=fmpq_mpoly(raw['common_denominator'],C)
    residues={(2*c+d+e)%6 for c,d,e in den.to_dict()}
    assert len(residues)==1
    rD=residues.pop();dd=descend(den,-rD)
    aa,bb,qq=s.symbols('a b q')
    fwords=[s.sympify(x,locals={'a':aa,'b':bb,'q':qq})for x in raw['f_words']]
    fexps=[s.Poly(x,aa,bb,qq).terms()[0][0]for x in fwords]
    ndG=[[descend(fmpq_mpoly(raw['gamma_numerators'][r][col],C),weights[col]-weights[r]-rD)for col in range(9)]for r in range(9)]
    ndP=[[descend(fmpq_mpoly(raw['primitive_numerators'][r][col],C),weights[col]-fexps[r][2]-3*fexps[r][1]+6-rD)for col in range(9)]for r in range(16)]
    all_dicts=[dd]+[x for row in ndG+ndP for x in row]
    minv=min(k[2]for dc in all_dicts for k in dc);offset=max(0,-minv)
    def mk(dc):return T.from_dict({(i,j,v+offset):co for (i,j,v),co in dc.items()})
    D=mk(dd);G=[[mk(x)for x in row]for row in ndG];P=[[mk(x)for x in row]for row in ndP]
    for k in range(9):G[k][k]+=weights[k]*D
    cp=ii-jj*jj/4;rr=cp*(cp-jj*jj)/8
    change=[[zero for _ in range(9)]for _ in range(9)];inv=[[zero for _ in range(9)]for _ in range(9)]
    order=[0,1,3,4,5,6,7,8,2]
    for col,row in enumerate(order):change[row][col]=one;inv[col][row]=one
    change[2][3]=-vv*rr;change[2][5]=jj/2
    inv[8][4]=vv*rr;inv[8][6]=-jj/2
    deriv=[[6*vv*D*z.derivative(2)for z in row]for row in change]
    G=matmul(inv,add(matmul(G,change),deriv));P=matmul(P,change)
    # Exact Cartan correction -i_(x*d/dx)nu.  The appended ninth
    # class is also retained, even though it is not compact.
    xN=[{(0,0,1):one},{(0,0,2):one},{(0,0,4):one},
        {(0,0,5):one,(0,0,3):-vv*rr},
        {(1,0,1):one},{(1,0,2):one,(0,0,3):jj/2},
        {(0,1,1):one},{(0,1,2):one},{(0,0,3):one}]
    indexes={x:r for r,x in enumerate(fexps)}
    for col,terms in enumerate(xN):
        for exponent,co in terms.items():P[indexes[exponent]][col]-=D*vv*co
    assert all(not x for x in G[8][:8]) and G[8][8]==3*D
    common=D
    for mat in (G,P):
        for row in mat:
            for x in row:
                common=common.gcd(x)
                if common==1:break
            if common==1:break
        if common==1:break
    D=D//common;G=[[x//common for x in row]for row in G];P=[[x//common for x in row]for row in P]
    independent=json.loads((THETA/'rank8-descended-connection-results.json').read_text())
    Dcheck=fmpq_mpoly(independent['GammaV_denominator'],T)
    for r in range(8):
        for col in range(8):assert G[r][col]*Dcheck==fmpq_mpoly(independent['GammaV_numerator'][r][col],T)*D,(r,col)
        assert G[r][8]*Dcheck==fmpq_mpoly(independent['omega_column_numerator'][r],T)*D
    words=[]
    for a,b,q in fexps:
        parts=[]
        for name,n in [('a',a),('y',b),('x',q)]:
            if n:parts.append(name if n==1 else name+'^'+str(n))
        words.append('*'.join(parts)or'1')
    out={
        'status':'Exact literal fixed-x V=6v*partial_v connection and fiber primitives; source not integrated',
        'direction':'V=6*v*partial_v at fixed(i,j,x)',
        'Jbar':'v*(2*a^2+j*a*x)-2*y^2',
        'common_denominator':str(D),
        'GammaV_numerators':[[str(x)for x in row[:8]]for row in G[:8]],
        'full_rank9_GammaV_numerators':[[str(x)for x in row]for row in G],
        'primitive_words':words,
        'primitive_convention':'primitive_V[col]=sum_word numerator[word,col]*word/(common_denominator*Jbar)',
        'primitive_numerators':[[str(x)for x in row[:8]]for row in P],
        'omega_primitive_numerators':[str(P[r][8])for r in range(16)],
        'source_affine_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
        'checks':{
            'all_333_original_generic_cleared_polynomial_identities':True,
            'every_deck_primitive_exponent_divisible_by_six':True,
            'negative_fiber_coordinate_Cartan_primitive_retained':True,
            'all_72_compact_and_omega_matrix_entries_match_existing_V_connection':True,
            'full_basis_change_V_derivative_retained':True,
            'compact_residue_row_zero_and_omega_diagonal_three':True},
        'certificate':False,'seconds':round(time.monotonic()-started,3)}
    path=HERE/'rank8-v-literal-primitives-results.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print('fixed-x V primitives saved; all72matrix matches exact',out['seconds'],flush=True)

if __name__=='__main__':main()
