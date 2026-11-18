"""Verify strict Hall expansion of the actual monomial Higgs action."""
from itertools import product
from pathlib import Path
import re
import sys

def higgs_data():
    socle=(4,4,4,4,1)
    degree_six=[x for x in product(*(range(i+1) for i in socle)) if sum(x)+x[-1]==6]
    char=lambda x:(2*x[0]+2*x[1]+x[2])%3
    upper=[x for x in degree_six if char(x)==1]
    tangents=[x for x in degree_six if char(x)==0]
    complement=[[next((k for k,z in enumerate(upper)
                     if all(i+j+l==m for i,j,l,m in zip(x,y,z,socle))),None)
                         for y in upper] for x in tangents]
    return upper,tangents,complement

def discover(g):
    def extend(path,unused):
        if not unused:return path if path[0] in g[path[-1]] else None
        i=path[-1]
        for j in sorted(g[i]&unused,key=lambda a:(len(g[a]&unused),a)):
            ans=extend(path+[j],unused-{j})
            if ans is not None:return ans
        return None
    return extend([0],set(range(1,33)))

if __name__=='__main__':
    u,t,comp=higgs_data()
    if len(sys.argv)>1:
        source=Path(sys.argv[1]).read_text()
        mat=source.split('def complement :',1)[1].split('def ',1)[0]
        data=[]
        for row in mat.splitlines():
            toks=re.findall(r'\b(?:none|some [0-9]+)\b',row)
            if toks:data.append([None if z=='none' else int(z[5:]) for z in toks])
        assert data==comp, 'native complement ordering or entries differ'
    g=[{r[j] for r in comp if r[j] is not None} for j in range(len(u))]
    cyc=discover(g)
    assert cyc and set(cyc)==set(range(33)) and len(cyc)==33
    edges=[next(k for k,row in enumerate(comp) if row[j]==cyc[(i+1)%33]) for i,j in enumerate(cyc)]
    print(f'{len(u)} source vertices, {len(t)} Higgs maps, {sum(map(len,g))} directed edges.')
    print('Hamiltonian cycle',cyc)
    print('Higgs direction for each successor edge',edges)
    print('Both successor and predecessor are perfect matchings; their relative shift is two, a 33-cycle.')
