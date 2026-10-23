"""Literal deck descent of both additional compact base connections.

The c,d derivative directions become partial_i=e^2 partial_c and
partial_j=e partial_d at fixed v.  Thus no moving fiber-coordinate Cartan
term is omitted in either direction.  Every original primitive is kept.
"""
import hashlib,json,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq

HERE=Path(__file__).resolve().parent
C=fmpq_mpoly_ctx.get(('c','d','e'))
T=fmpq_mpoly_ctx.get(('i','j','v'))
ii,jj,vv=T.gens();zero=T.constant(0);one=T.constant(1)
weights=[1,2,3,4,5,1,2,4,5]

def descend(poly,shift):
    result={}
    for (c,d,e),co in poly.to_dict().items():
        n=2*c+d+e+shift
        assert n%6==0,(c,d,e,shift)
        key=(c,d,n//6)
        result[key]=result.get(key,fmpq(0))+co
    return result

def matmul(A,B):
    return [[sum((a*b for a,b in zip(ar,bc)),zero)for bc in zip(*B)]for ar in A]
def add(A,B):return [[a+b for a,b in zip(ar,br)]for ar,br in zip(A,B)]

def main():
    started=time.monotonic()
    source=HERE/'affine-cd-generic-results.json'
    raw=json.loads(source.read_text())
    assert raw['all_666_generic_cleared_polynomial_identities']
    den=fmpq_mpoly(raw['common_denominator'],C)
    residues={(2*c+d+e)%6 for c,d,e in den.to_dict()}
    assert len(residues)==1
    residue=residues.pop()
    dd=descend(den,-residue)
    aa,bb,qq=s.symbols('a b q')
    fwords=[s.sympify(x,locals={'a':aa,'b':bb,'q':qq})for x in raw['primitive_words']]
    fexps=[]
    for f in fwords:
        terms=s.Poly(f,aa,bb,qq).terms()
        assert len(terms)==1 and terms[0][1]==1
        fexps.append(terms[0][0])
    descG={};descP={}
    all_dicts=[dd]
    for name,key,degree in [('i','c',2),('j','d',1)]:
        G=[[descend(fmpq_mpoly(raw['gamma_numerators'][key][r][col],C),
                    weights[col]+degree-weights[r]-residue)
            for col in range(9)]for r in range(9)]
        P=[[descend(fmpq_mpoly(raw['primitive_numerators'][key][r][col],C),
                    weights[col]+degree-fexps[r][2]-3*fexps[r][1]+6-residue)
            for col in range(9)]for r in range(16)]
        descG[name]=G;descP[name]=P
        all_dicts.extend(dc for row in G+P for dc in row)
    minv=min(k[2]for dc in all_dicts for k in dc)
    offset=max(0,-minv)
    def mk(dc):return T.from_dict({(i,j,v+offset):co for (i,j,v),co in dc.items()})
    D=mk(dd)
    G={name:[[mk(x)for x in row]for row in mat]for name,mat in descG.items()}
    P={name:[[mk(x)for x in row]for row in mat]for name,mat in descP.items()}

    cp=ii-jj*jj/4
    rr=cp*(cp-jj*jj)/8
    change=[[zero for _ in range(9)]for _ in range(9)]
    inv=[[zero for _ in range(9)]for _ in range(9)]
    order=[0,1,3,4,5,6,7,8,2]
    for col,row in enumerate(order):change[row][col]=one;inv[col][row]=one
    change[2][3]=-vv*rr;change[2][5]=jj/2
    inv[8][4]=vv*rr;inv[8][6]=-jj/2
    assert matmul(inv,change)==[[one if r==c else zero for c in range(9)]for r in range(9)]
    for name,var in [('i',0),('j',1)]:
        derivative=[[D*z.derivative(var)for z in row]for row in change]
        G[name]=matmul(inv,add(matmul(G[name],change),derivative))
        P[name]=matmul(P[name],change)
        assert all(not z for z in G[name][8]),name

    # One shared denominator for both matrices and all exact primitives.
    common=D
    for mat in list(G.values())+list(P.values()):
        for ar in mat:
            for z in ar:
                common=common.gcd(z)
                if common==1:break
            if common==1:break
        if common==1:break
    D=D//common
    G={k:[[z//common for z in row]for row in mat]for k,mat in G.items()}
    P={k:[[z//common for z in row]for row in mat]for k,mat in P.items()}
    descended_words=[]
    for a,b,q in fexps:
        terms=[]
        for symbol,n in [('a',a),('y',b),('x',q)]:
            if n:terms.append(symbol if n==1 else symbol+'^'+str(n))
        descended_words.append('*'.join(terms)or'1')
    result={
        'status':'Exact generic full-base compact connections in i,j, with all rational fiber primitives; actual source not integrated',
        'coordinates':'i=c/e^2,j=d/e,v=e^6; partial_i at fixed(j,v), partial_j at fixed(i,v)',
        'descended_curve':['a*y=x^3','y^2+v*(a^2+i*x^2+j*a*x+x+1)=0'],
        'Jbar':'v*(2*a^2+j*a*x)-2*y^2',
        'compact_basis_numerators':['1','x','x^3','x^4-v*(i-j^2/4)*(i-5*j^2/4)*x^2/8','a','a*x+j*x^2/2','y','y*x'],
        'basis_convention':'nu_N=v*N*dx/Jbar; appended ninth omega=v*x^2*dx/Jbar',
        'connection_convention':'partial_p nu_col=sum_row Gamma_p[row,col]*nu_row+d_x(primitive_p[col]); columns differentiate basis forms',
        'common_denominator':str(D),
        'Gamma_numerators':{name:[[str(z)for z in row[:8]]for row in G[name][:8]]for name in ('i','j')},
        'omega_column_numerators':{name:[str(G[name][r][8])for r in range(8)]for name in ('i','j')},
        'full_rank9_Gamma_numerators':{name:[[str(z)for z in row]for row in G[name]]for name in ('i','j')},
        'primitive_words':descended_words,
        'primitive_convention':'primitive_p[col]=sum_word primitive_numerators[p][word,col]*word/(common_denominator*Jbar)',
        'primitive_numerators':{name:[[str(z)for z in row[:8]]for row in P[name]]for name in ('i','j')},
        'omega_primitive_numerators':{name:[str(P[name][r][8])for r in range(16)]for name in ('i','j')},
        'source_affine_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'checks':{
            'all_666_original_generic_cleared_polynomial_identities':True,
            'every_deck_exponent_divisible_by_six':True,
            'full_primitive_deck_descent':True,
            'exact_compact_basis_change_inverse':True,
            'full_basis_change_i_j_derivatives_retained':True,
            'both_residue_rows_identically_zero':True,
            'no_moving_fiber_coordinate_in_i_j_directions':True},
        'certificate':False,
        'seconds':round(time.monotonic()-started,3)
    }
    out=HERE/'rank8-ij-connections-results.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('saved literal rank8 i,j connections+fiber primitives',result['seconds'],flush=True)
    print('denominator degrees',D.degrees(),'terms',len(D.to_dict()),flush=True)

if __name__=='__main__':main()
