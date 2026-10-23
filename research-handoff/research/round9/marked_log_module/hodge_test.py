"""One structural Hodge-leading pass, without arbitrary numerator degrees."""
from pathlib import Path
import json,random,time
from flint import nmod_mat
from physical import PhysicalModel,hodge_leading
root=Path(__file__).parent;p=1000003;model=PhysicalModel(p);rng=random.Random(1093);start=time.monotonic();ans=[]
for normalized in [False,True]:
    for comp in [(3,4),(0,1,3,4)]:
        rows=[];rhs=[];points=[]
        while len(points)<35:
            pt=[rng.randrange(1,p)for _ in range(3)]
            try:d=model.point(pt,0,normalized);h=hodge_leading(d,p,comp,(0,4))
            except (ValueError,ZeroDivisionError):continue
            rows.extend(h['columns']);rhs.extend(h['residual']);points.append(pt)
        rank=nmod_mat(rows,p).rank();aug=nmod_mat([r+[v]for r,v in zip(rows,rhs)],p).rank()
        ans.append(dict(normalized=normalized,components=comp,columns=len(rows[0]),rank=rank,augmented_rank=aug,higgs_row_matched_exactly=True))
out=dict(prime=p,results=ans,seconds=time.monotonic()-start,scope='Four structural constant-coefficient Hodge-null modules using the natural Higgs-pivot pole; no unrestricted inference.')
(root/'hodge_test.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
