"""Full-source q=1 image for one selected moving-Segre cubic.

All source degree-six polynomials and all N degree-four fields are included.
There are no degree-nine Jacobian Koszul syzygies for a smooth sextic.
"""
from pathlib import Path
import json,pickle,time
import sympy as s
import yaml
from flint import nmod_mat

HERE=Path(__file__).parent
start=time.monotonic()
prime=1000033
ii=int(s.sqrt_mod(-1,prime))
z=s.symbols("X0 X1 X2 Y0 Y1 Y2")
rec=yaml.safe_load(Path('/workspace/sextics/data/eight-plane-configuration/instance.rec').read_text())
F=s.Poly(rec['F'],*z)
def exps(d,n=6):
    if n==1:
        yield (d,);return
    for j in range(d+1):
        for tail in exps(d-j,n-1):
            yield (j,)+tail
def mod(c):
    c=s.expand(c).subs(s.I,ii)
    a,b=s.fraction(c)
    return int(a)%prime*pow(int(b)%prime,-1,prime)%prime
def pd(p):
    return {e:mod(c) for e,c in s.Poly(p,*z).terms() if mod(c)}
U=s.Matrix([z[j]+s.I*z[j+3] for j in range(3)])
V=s.Matrix([z[j]-s.I*z[j+3] for j in range(3)])
M1=s.Matrix([[1,2,3],[0,2,1],[1,0,3]])
D=s.expand(s.Matrix.hstack(U,V,M1*V).det())
dd=pd(D)
fm=pd(F.as_expr())
nj=list(exps(4));am=list(exps(6));out=list(exps(9))
outind={e:i for i,e in enumerate(out)}
sourceind={e:i for i,e in enumerate(am)}
nc=6*len(nj);na=len(am)
matrix=[[0]*(nc+na) for _ in out]
for i in range(6):
    fi=pd(F.diff(z[i]).as_expr())
    for j,m in enumerate(nj):
        for e,c in fi.items():
            ee=tuple(a+b for a,b in zip(e,m))
            matrix[outind[ee]][i*len(nj)+j]=c
for j,m in enumerate(am):
    for e,c in dd.items():
        ee=tuple(a+b for a,b in zip(e,m))
        matrix[outind[ee]][nc+j]=-c%prime
A=nmod_mat(matrix,prime)
del matrix
ker,k=A.nullspace()
NK=nmod_mat([[int(ker[i,j]) for j in range(k)] for i in range(nc)],prime)
AK=nmod_mat([[int(ker[nc+i,j]) for j in range(k)] for i in range(na)],prime)
print('E1 nullity',k,'seconds',time.monotonic()-start,flush=True)

# Complete E2 modulo F: D divN - N(D)=constant*F.  Retain this quotient.
BD=[[0]*nc for _ in am]
gradD=[pd(s.diff(D,z[i])) for i in range(6)]
for i in range(6):
    for j,m in enumerate(nj):
        col=i*len(nj)+j
        for e,c in gradD[i].items():
            ee=tuple(a+b for a,b in zip(e,m))
            row=sourceind[ee]
            BD[row][col]=(BD[row][col]-c)%prime
        if m[i]:
            mm=list(m);mm[i]-=1
            for e,c in dd.items():
                ee=tuple(a+b for a,b in zip(e,mm))
                row=sourceind[ee]
                BD[row][col]=(BD[row][col]+m[i]*c)%prime
BB=nmod_mat(BD,prime)*NK
E2=nmod_mat([[int(BB[i,j]) for j in range(k)]+[-fm.get(m,0)%prime]
             for i,m in enumerate(am)],prime)
K2,n2=E2.nullspace()
src=AK*nmod_mat([[int(K2[i,j]) for j in range(n2)] for i in range(k)],prime)
W,wrank=nmod_mat([[int(src[i,j]) for i in range(na)] for j in range(n2)],prime).rref()
wrows=[[int(W[i,j]) for j in range(na)] for i in range(wrank)]
signs=[-1 if sum(e[3:])%2 else 1 for e in am]
twrows=[[(c*sgn)%prime for c,sgn in zip(row,signs)] for row in wrows]
target=[0]*na;target[sourceind[(3,0,0,3,0,0)]]=1
union=nmod_mat(wrows+twrows,prime).rank()
aug=nmod_mat(wrows+twrows+[target],prime).rank()
ans=dict(prime=prime,i_value=ii,D=str(D),M0='identity',M1=[[int(x) for x in M1.row(j)] for j in range(3)],
         E1_rows=len(out),E1_columns=nc+na,E1_rank=nc+na-k,E1_nullity=k,
         E2_rows=na,E2_columns=k+1,E2_rank=k+1-n2,
         served_source_dimension=wrank,union_dimension=union,
         union_target_augmented_rank=aug,target_in_union_modp=(union==aug),
         seconds=time.monotonic()-start,
         regular_exact_sources_dimension=35,
         scope='Selected moving-Segre cubic and its global-Y translate only; finite-prime image unless stated exact by a rank sandwich.')
if k==36 and wrank==35:
    ans['exact_rank_sandwich']='E1 kernel is exactly the 36 linear-field sources; E2 leaves exactly the 35 tracezero linear fields. Thus this selected cubic has only the globally exact source image over C, and its translate adds nothing.'
(HERE/'moving_segre_cubic.json').write_text(json.dumps(ans,indent=2)+'\n')
(HERE/'moving_segre_cubic_mod.pickle').write_bytes(pickle.dumps(dict(
    prime=prime,D=D,source_monomials=am,source_basis=wrows,translated_basis=twrows)))
print(json.dumps(ans,indent=2),flush=True)
