#!/usr/bin/env python3
"""Compare projected kernels with independent dense Python RREF."""
from pathlib import Path
import json,random,struct,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
p=1009
def rref(matrix,n):
    a=[row[:] for row in matrix];rank=0;piv=[]
    for j in range(n):
        k=next((k for k in range(rank,len(a)) if a[k][j]),None)
        if k is None:continue
        a[rank],a[k]=a[k],a[rank]
        inv=pow(a[rank][j],-1,p);a[rank]=[v*inv%p for v in a[rank]]
        for k in range(len(a)):
            if k!=rank and a[k][j]:
                f=a[k][j];a[k]=[(x-f*y)%p for x,y in zip(a[k],a[rank])]
        piv.append(j);rank+=1
        if rank==len(a):break
    return a[:rank],piv
reports=[]
for case,(m,n) in enumerate([(12,30),(24,30),(40,30),(20,36),(30,36),(45,36)]):
    rng=random.Random(791+case)
    a=[[rng.randrange(p) if rng.random()<.22 else 0 for _ in range(n)] for _ in range(m)]
    if case in [1,4]:
        for row in a:row[-1]=(row[0]+3*row[1])%p
    rr,piv=rref(a,n);free=[j for j in range(n) if j not in piv]
    null=[]
    for j in free:
        v=[0]*n;v[j]=1
        for i,k in enumerate(piv):v[k]=-rr[i][j]%p
        null.append(v[-24:])
    expected,_=rref(null,24)
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/'test.bin';out=Path(tmp)/'out.json'
        with path.open('wb') as f:
            f.write(struct.pack('<4I',m,n,p,sum(bool(v) for row in a for v in row)))
            for j in range(n):
                col=[(i,row[j]) for i,row in enumerate(a) if row[j]]
                f.write(struct.pack('<I',len(col)))
                for pair in col:f.write(struct.pack('<II',*pair))
            f.write(struct.pack('<I',0))
        subprocess.run([str(ROOT/'project_sources'),str(path),str(out),'30','300'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
        got=json.loads(out.read_text())
        assert got['rank']==len(piv)
        assert got['kernel_dimension']==len(free)
        assert got['source_basis']==expected,(case,got['source_basis'],expected)
        assert got['served_source_dimension']==len(expected)
    reports.append({'case':case,'rows':m,'columns':n,'rank':len(piv),'served_dimension':len(expected),'status':'passed'})
(ROOT/'projection-selftest.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports))
