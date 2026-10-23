from pathlib import Path
import sys,json,time,argparse
import numpy as np
sys.path.insert(0,'/workspace/off-paired-research-published')
import ansatz as a
root=Path(__file__).parent

def solve_matrix(mat,rhs,p):
    aug=np.column_stack((mat,rhs));m,n=mat.shape;r=0;piv=[]
    for col in range(n):
        nz=np.flatnonzero(aug[r:,col])
        if not len(nz):continue
        k=r+int(nz[0]);aug[[r,k]]=aug[[k,r]]
        aug[r]=aug[r]*pow(int(aug[r,col]),-1,p)%p
        ids=np.flatnonzero(aug[r+1:,col])+r+1
        for st in range(0,len(ids),128):
            ii=ids[st:st+128];aug[ii]=(aug[ii]-aug[ii,col,None]*aug[r])%p
        piv.append(col);r+=1
        if r==m:break
    bad=np.flatnonzero(np.all(aug[:,:n]==0,axis=1)&(aug[:,n]!=0))
    if len(bad):return r,None
    sol=np.zeros(n,dtype=np.int64)
    for rr,cc in reversed(list(enumerate(piv))):sol[cc]=(aug[rr,n]-int(aug[rr,cc+1:n]@sol[cc+1:])%p)%p
    assert np.all((mat@sol-rhs)%p==0)
    return r,sol

def run(k,p):
    f={(1,0,0,0,1,0):a.Q(3),(0,0,1,0,0,1):a.Q(2)}
    D={(0,0,0,0,0,0):a.Q(1)}
    for _ in range(k):D=a.mul(D,f)
    start=time.monotonic();cols,rhs,rows,names=a.system(D)
    ids={e:i for i,e in enumerate(rows)}
    mat=np.zeros((len(rows),len(cols)),dtype=np.int64)
    rr=np.zeros(len(rows),dtype=np.int64)
    cv=lambda c:c.numerator*pow(c.denominator,-1,p)%p
    for j,col in enumerate(cols):
        for e,c in col.items():mat[ids[e],j]=cv(c)
    for e,c in rhs.items():rr[ids[e]]=cv(c)
    print(json.dumps({'k':k,'phase':'matrix','rows':len(rows),'cols':len(cols),'seconds':time.monotonic()-start}),flush=True)
    rank,sol=solve_matrix(mat,rr,p)
    out={'denominator':'(3*X0*Y1+2*X2*Y2)**'+str(k),'k':k,'degree':2*k,'prime':p,'rows':len(rows),'unknowns':len(cols),'rank':rank,'consistent':sol is not None,'seconds':time.monotonic()-start,'scope':'Full homogeneous numerators and quotient in exact diagonal-character block for this fixed denominator; modular search only.'}
    if sol is not None:
        out['candidate']=[{'name':name,'monomial':e,'coefficient':int(c)}for(name,e),c in zip(names,sol)if c]
    print(json.dumps(out),flush=True)
    return out

if __name__=='__main__':
    par=argparse.ArgumentParser();par.add_argument('--powers',type=int,nargs='+',default=[4,5]);par.add_argument('--prime',type=int,default=1009);par.add_argument('--output',default='endpoint-cancellation-denominator-results.json');args=par.parse_args()
    output=[]
    for k in args.powers:
        output.append(run(k,args.prime))
        (root/args.output).write_text(json.dumps(output,indent=2))
        if output[-1]['consistent']:break
