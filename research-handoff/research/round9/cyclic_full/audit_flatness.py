"""Independent exact curvature check using native polynomial common denominators."""
import json,pickle,time
from pathlib import Path
import sympy as S
from flint import fmpq_mpoly_ctx,fmpq
HERE=Path(__file__).resolve().parent;ctx=fmpq_mpoly_ctx.get(('L','r','x'));start=time.monotonic()
def poly(expr,base):return ctx.from_dict({m:fmpq(str(c))for m,c in S.Poly(expr,*base).as_dict().items()})
def matrix_data(N,base):
    pairs=[];D=ctx.constant(1)
    for expr in N:
        p,q=S.fraction(expr);pp,qq=poly(p,base),poly(q,base);pairs.append((pp,qq));D*=qq//D.gcd(qq)
    return D,[[pairs[3*i+j][0]*(D//pairs[3*i+j][1])for j in range(3)]for i in range(3)]
report={}
for tag in ('actual','conjugate'):
    obj=pickle.load(open(HERE/(tag+'_fast.pickle'),'rb'));base=obj['symbols'][3:];data=[matrix_data(obj['connection'][str(z)],base)for z in base]
    results={}
    for i in range(3):
        for j in range(i+1,3):
            Di,Pi=data[i];Dj,Pj=data[j];nonzero=[]
            for a in range(3):
                for b in range(3):
                    derivative_j=Pi[a][b].derivative(j)*Di-Pi[a][b]*Di.derivative(j)
                    derivative_i=Pj[a][b].derivative(i)*Dj-Pj[a][b]*Dj.derivative(i)
                    commutator=sum(Pj[a][k]*Pi[k][b]-Pi[a][k]*Pj[k][b]for k in range(3))
                    numerator=Di**2*derivative_i-Dj**2*derivative_j+Di*Dj*commutator
                    if numerator:nonzero.append((a,b,len(numerator)))
            assert not nonzero,(tag,i,j,nonzero)
            results[str((str(base[i]),str(base[j])))]=True
            print('EXACT_FLAT',tag,base[i],base[j],time.monotonic()-start,flush=True)
    report[tag]={'exact_curvature_zero':results,'matrix_common_denominator_degrees':[list(map(int,D.degrees()))for D,P in data],'matrix_common_denominator_terms':[len(D)for D,P in data]}
report['seconds']=time.monotonic()-start;report['convention']='d_i N_j-d_j N_i+N_j N_i-N_i N_j'
(HERE/'flatness_audit.json').write_text(json.dumps(report,indent=2)+'\n')
