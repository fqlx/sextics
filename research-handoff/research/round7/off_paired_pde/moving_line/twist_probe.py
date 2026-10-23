from pathlib import Path
import json,itertools
p=json.load(open('/workspace/research/round7/moving_j1728/squareclass_probe.json'));prime=p['prime']
features=[('v',lambda d:d['v']),('v-1',lambda d:d['v']-1),('v+1',lambda d:d['v']+1),('2v²-1',lambda d:2*d['v']**2-1),('v²+1',lambda d:d['v']**2+1),('v²+3',lambda d:d['v']**2+3),('t',lambda d:d['t']),('h-2',lambda d:d['h']-2),('h+2',lambda d:d['h']+2),('h',lambda d:d['h'])]
qs=sorted(set(d['q']for d in p['points']));rows=[];used=[]
for d in p['points']:
 vals=[fn(d)%prime for _,fn in features]
 if not all(vals):continue
 bits=[int(pow(v,(prime-1)//2,prime)!=1)for v in vals]+[int(d['q']==q)for q in qs]+[int(d['chi_alpha']==-1)]
 rows.append(sum(b<<i for i,b in enumerate(bits)));used.append(d)
n=len(features)+len(qs);rr=rows[:];piv=[];i=0
for j in range(n):
 k=next((k for k in range(i,len(rr))if rr[k]>>j&1),None)
 if k is None:continue
 rr[i],rr[k]=rr[k],rr[i]
 for k in range(len(rr)):
  if k!=i and rr[k]>>j&1:rr[k]^=rr[i]
 piv.append(j);i+=1
bad=any(v&((1<<n)-1)==0 and v>>n&1 for v in rr)
out={'prime':prime,'points_used':len(used),'features':[n for n,_ in features],'rank':len(piv),'consistent':not bad,'scope':'Finite-field candidate screen; not a complex squareclass theorem'}
if not bad:
 sol=[0]*n
 for row,pivot in zip(rr,piv):sol[pivot]=row>>n&1
 out['candidate_features']=[features[j][0]for j in range(len(features))if sol[j]]
 out['q_character_values']={q:sol[len(features)+j]for j,q in enumerate(qs)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
