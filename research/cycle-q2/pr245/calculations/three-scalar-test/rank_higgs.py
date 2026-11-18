from itertools import product
p=101
def mons(k):
 return [(i,j,k-i-j) for i in range(k+1) for j in range(k-i+1)]
m9=mons(9); m4=mons(4)
A,B,C=2,3,5
fx={(5,0,0):6*B,(0,1,4):1,(0,0,5):1};fy={(0,5,0):6*A,(1,0,4):1,(0,0,5):1}
fz={(1,1,3):4,(1,0,4):5,(0,1,4):5,(0,0,5):6*C}
def rank(rows):
 vals={}
 for row in rows:
  r=row[:]
  for k in range(len(r)):
   if not r[k]%p:continue
   if k not in vals:
    inv=pow(r[k],-1,p)
    vals[k]=[a*inv%p for a in r];break
   ri=r[k]
   for i in range(k,len(r)):r[i]=(r[i]-ri*vals[k][i])%p
 return len(vals)
rows=[]
for a in m4:
 for f in (fx,fy,fz):
  rows.append([f.get(tuple(zi-ai for zi,ai in zip(z,a)),0) for z in m9])
print('Jac9 rank', rank(rows))
for z in [(6,0,3),(0,6,3),(0,0,9)]:
 rows.append([int(z==v) for v in m9])
 print(z,rank(rows))
