"""Source-specific weighted current screen with the two boundary sextics.

The two pole supports are g0(a,b)=0 and g3(c,d)=0.  The bidegree bounds
come from the homogeneous current weights; the affine feature space permits
all smaller bidegrees as well.  This is a bounded positive candidate search,
not an existence/nonexistence theorem for arbitrary currents.
"""
import os
os.environ["EIGHT_MODEL"]="cubic"
import current_search as m
import json,pickle,random,time
from flint import nmod_mat

def bipolys(du,dv):
    if min(du,dv)<0:
        return []
    return [(a,b,c,d) for a in range(du+1) for b in range(du+1-a)
            for c in range(dv+1) for d in range(dv+1-c)]

features=[]
for support,wu,wv in (("regular",0,0),("g0",6,0),("g3",0,6)):
    for i in range(4):
        for j in range(3):
            du=(2 if i<2 else 1)+wu-2*j
            dv=(-1 if i<2 else 0)+wv+2*j
            for e in bipolys(du,dv):
                features.append((i,j,e,support))

def block(point,data):
    C,D,rhs,extra=data
    gs,gg=extra['g'],extra['derivatives']
    p=m.prime
    powers=[[pow(x,j,p) for j in range(9)] for x in point]
    rows=[[] for _ in range(3)]
    for i,j,e,support in features:
        val=1
        for k in range(4):
            val=val*powers[k][e[k]]%p
        derivative=0
        if e[i]:
            derivative=e[i]
            for k in range(4):
                derivative=derivative*powers[k][e[k]-(i==k)]%p
        if support=='regular':
            invt,logd=1,0
        else:
            idx=0 if support=='g0' else 3
            if not gs[idx]:
                return None
            invt=pow(gs[idx],-1,p)
            logd=gg[i][idx]*invt%p
        derivative=(derivative-val*logd)%p
        for r in range(3):
            rows[r].append((val*C[i][j][r]+derivative*D[j][r])*invt%p)
    return [row+[rhs[i]] for i,row in enumerate(rows)]

start=time.monotonic()
rng=random.Random(80128912)
rows=[];points=[]
for _ in range(len(features)//2+30):
    while True:
        point=tuple(rng.randrange(1,m.prime) for _ in range(4))
        data=m.evaluate(point)
        if data is not None:
            out=block(point,data)
            if out is not None:
                break
    points.append(point);rows.extend(out)
rr,rank=nmod_mat(rows,m.prime).rref()
coefficient_rank=sum(any(int(rr[i,j]) for j in range(len(features))) for i in range(rank))
ans=dict(prime=m.prime,features=len(features),rows=len(rows),rank=coefficient_rank,
         augmented_rank=rank,consistent=(rank==coefficient_rank),
         source='N=t^2, normalized residue (Nprime*Cprime-N*Csecond)/(Cprime)^3',
         denominator='Cprime times 1, g0, or g3',
         seconds=time.monotonic()-start,
         scope='Finite-field screen of the listed weighted feature space only.')
if ans['consistent']:
    sol=[0]*len(features)
    for i in range(rank):
        pivot=next(j for j in range(len(features)) if int(rr[i,j]))
        sol[pivot]=int(rr[i,len(features)])
    valid=True
    for _ in range(300):
        point=tuple(rng.randrange(1,m.prime) for _ in range(4))
        data=m.evaluate(point)
        if data is None:
            continue
        out=block(point,data)
        if out is None:
            continue
        if any((sum(a*b for a,b in zip(row[:-1],sol))-row[-1])%m.prime for row in out):
            valid=False;break
    ans['independent_300_fibers_pass']=valid
    if valid:
        (m.HERE/'cubic_weighted_poles_candidate.pickle').write_bytes(pickle.dumps(
            dict(prime=m.prime,features=features,solution=sol,points=points)))
(m.HERE/'cubic_weighted_poles.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps(ans,indent=2),flush=True)
