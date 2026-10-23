"""Complete q1 E2 completion for D=E_Y(F), with its known E1 lift.

N=A*E_Y satisfies N(F)=A*D.  Every ambiguity is a Jacobian Koszul
pair times a homogeneous quadratic, because the six partials are regular.
The quotient F*Q6 in the E2 equation is retained.
"""
from pathlib import Path
import json,pickle,time,sys
import sympy as s,yaml
from flint import nmod_mpoly_ctx,nmod_mat

HERE=Path(__file__).parent
start=time.monotonic();prime=1000003
names=['X0','X1','X2','Y0','Y1','Y2'];z=s.symbols(' '.join(names))
block=tuple(map(int,sys.argv[1:])) or (3,4,5)
assert len(block)==3 and len(set(block))==3 and all(0<=i<6 for i in block)
assert len(set(block)&{0,3})==1
rec=yaml.safe_load(Path('/workspace/sextics/data/eight-plane-configuration/instance.rec').read_text())
ctx=nmod_mpoly_ctx.get(names,prime,'degrevlex');x=ctx.gens()
def coeff(c):
    a,b=map(int,s.fraction(c));return a%prime*pow(b%prime,-1,prime)%prime
def convert(expr):
    return ctx.from_dict({e:coeff(c) for e,c in s.Poly(expr,*z).terms()})
F=convert(s.sympify(rec['F']));A=convert(s.sympify(rec['A']))
Fi=[F.derivative(i) for i in range(6)]
D=sum((x[i]*Fi[i] for i in block),ctx.constant(0))
Di=[D.derivative(i) for i in range(6)]
EYD=sum((x[i]*Di[i] for i in block),ctx.constant(0))
rhs=-A*(6*D-EYD)
def exps(d,n=6):
    if n==1:
        yield(d,);return
    for j in range(d+1):
        for tail in exps(d-j,n-1):yield(j,)+tail
def mono(e):return ctx.from_dict({e:1})
mons2=list(exps(2));mons6=list(exps(6));rows=list(exps(12));ri={e:i for i,e in enumerate(rows)}
nsy=15*len(mons2);nc=nsy+len(mons6)
mat=[[0]*(nc+1) for _ in rows]
col=0;features=[]
for i in range(6):
    for j in range(i+1,6):
        for e in mons2:
            m=mono(e)
            L=Fi[j]*(D*m.derivative(i)-m*Di[i])-Fi[i]*(D*m.derivative(j)-m*Di[j])
            for ee,c in L.to_dict().items():mat[ri[ee]][col]=int(c)
            features.append((i,j,e));col+=1
for e in mons6:
    L=-F*mono(e)
    for ee,c in L.to_dict().items():mat[ri[ee]][col]=int(c)
    col+=1
for ee,c in rhs.to_dict().items():mat[ri[ee]][nc]=int(c)
rr,rank=nmod_mat(mat,prime).rref()
cr=sum(any(int(rr[i,j]) for j in range(nc)) for i in range(rank))
ans=dict(prime=prime,support='D=E_block(F)',block=[names[i] for i in block],degree_D=6,
         E1_lift='N=A*E_block',E1_identity=True,
         numerator_completion='all 15 Jacobian Koszul pairs times all 21 quadratics',
         koszul_columns=nsy,quotient_columns=len(mons6),rows=len(rows),
         coefficient_rank=cr,augmented_rank=rank,consistent=(rank==cr),
         seconds=time.monotonic()-start,
         scope='Complete single-support q1 E2 system over the good finite prime; no arbitrary-support conclusion.')
if cr==nc-35 and rank==cr+1:
    ans['exact_rank_sandwich']='The 35 independent projective gauge kernels T=F*V-V(F)*Euler/6 bound rank by742 over Q; the bound is attained modulo p and the source augments rank. Hence no certificate for this selected D over C.'
tag='_'.join(names[i] for i in block)
if rank==cr:
    sol=[0]*nc
    for i in range(rank):
        pivot=next(j for j in range(nc) if int(rr[i,j]))
        sol[pivot]=int(rr[i,nc])
    (HERE/f'euler_support_{tag}_candidate.pickle').write_bytes(pickle.dumps(
        dict(prime=prime,solution=sol,koszul_features=features,quotient_monomials=mons6)))
(HERE/f'euler_support_{tag}.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps(ans,indent=2),flush=True)
