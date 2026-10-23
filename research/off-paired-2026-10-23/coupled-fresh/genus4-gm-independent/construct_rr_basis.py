"""Complete genus-four RR basis, exact finite-field chart/pivot witness.

This is not a bounded primitive search.  Riemann--Roch gives the prescribed
spaces H0(K+5P) (dimension 8) and L(J+4P) (dimension 13).  The first is built
here from homogeneous degree-six numerators divided by q^5.  The fixed
physical specialization is used only to exhibit generic nonzero pivots.
"""
import json
from pathlib import Path

p=1009
A=B=T=2
C=pow(3,-1,p)
D=E=pow(2,-1,p)
ORDER=6

def inv(x):return pow(x%p,-1,p)
def add(x,y):return [(a+b)%p for a,b in zip(x,y)]
def neg(x):return [-a%p for a in x]
def scale(x,a):return [v*a%p for v in x]
def mul(x,y):return [sum(x[j]*y[i-j] for j in range(i+1))%p for i in range(ORDER)]
def power(x,n):
 ans=[1]+[0]*(ORDER-1)
 while n:
  if n&1:ans=mul(ans,x)
  x=mul(x,x);n//=2
 return ans
def recip(x):
 out=[inv(x[0])]+[0]*(ORDER-1)
 for n in range(1,ORDER):out[n]=-out[0]*sum(x[j]*out[n-j]for j in range(1,n+1))%p
 return out
one=[1]+[0]*(ORDER-1)
zero=[0]*ORDER
u=[0,1]+[0]*(ORDER-2)
def quad(a,b,q,t):
 return add(add(add(scale(mul(a,a),A),scale(mul(b,b),B)),
                add(scale(mul(q,q),C),scale(mul(a,q),D))),
            add(scale(mul(q,t),E),scale(mul(t,t),T)))

def branch(kind,root):
 unknown=[root]+[0]*(ORDER-1)
 for n in range(1,ORDER):
  if kind=='a':a=unknown;b=mul(power(u,3),recip(a));t=one;der=2*A*root
  elif kind=='b':b=unknown;a=mul(power(u,3),recip(b));t=one;der=2*B*root
  else:a=one;b=unknown;t=mul(power(u,3),recip(b));der=2*B*root
  unknown[n]=-quad(a,b,u,t)[n]*inv(der)%p
 if kind=='a':a=unknown;b=mul(power(u,3),recip(a));t=one
 elif kind=='b':b=unknown;a=mul(power(u,3),recip(b));t=one
 else:a=one;b=unknown;t=mul(power(u,3),recip(b))
 assert quad(a,b,u,t)==zero
 assert add(mul(mul(a,b),t),neg(power(u,3)))==zero
 return [a,b,u,t]

def exponents(n):
 return [(a,b,q,n-a-b-q) for a in range(n+1)for b in range(n+1-a)for q in range(n+1-a-b)]
def rref(rows,width):
 a=[[x%p for x in row]for row in rows];piv=[];r=0
 for c in range(width):
  k=next((k for k in range(r,len(a))if a[k][c]),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r];a[r]=[v*inv(a[r][c])%p for v in a[r]]
  for k in range(len(a)):
   if k!=r and a[k][c]:
    f=a[k][c];a[k]=[(x-f*y)%p for x,y in zip(a[k],a[r])]
  piv.append(c);r+=1
  if r==len(a):break
 return a[:r],piv
def kernel(rows,width):
 rr,piv=rref(rows,width);free=[c for c in range(width)if c not in piv];out=[]
 for f in free:
  v=[0]*width;v[f]=1
  for row,c in zip(rr,piv):v[c]=-row[f]%p
  out.append(v)
 return out,piv
def det(mat):
 a=[row[:]for row in mat];ans=1
 for c in range(len(a)):
  k=next((k for k in range(c,len(a))if a[k][c]),None)
  if k is None:return 0
  if k!=c:a[k],a[c]=a[c],a[k];ans=-ans
  f=a[c][c];ans=ans*f%p
  for k in range(c+1,len(a)):
   g=a[k][c]*inv(f)%p
   a[k]=[(x-g*y)%p for x,y in zip(a[k],a[c])]
 return ans%p

mon6=exponents(6);ix={m:i for i,m in enumerate(mon6)}
Q={(2,0,0,0):A,(0,2,0,0):B,(0,0,2,0):C,(1,0,1,0):D,(0,0,1,1):E,(0,0,0,2):T}
C1={(1,1,0,1):1,(0,0,3,0):-1}
relations=[]
for form,degree in ((Q,4),(C1,3)):
 for m in exponents(degree):
  row=[0]*len(mon6)
  for n,coef in form.items():row[ix[tuple(x+y for x,y in zip(m,n))]]=coef%p
  relations.append(row)
rr,ipiv=rref(relations,len(mon6))
quotcols=[c for c in range(len(mon6))if c not in ipiv]
assert len(quotcols)==33

root=next(x for x in range(p)if x*x%p==(-T*inv(A))%p)
rootb=next(x for x in range(p)if x*x%p==(-T*inv(B))%p)
rooti=next(x for x in range(p)if x*x%p==(-A*inv(B))%p)
labels=[('a',root),('a',-root%p),('b',rootb),('b',-rootb%p),('inf',rooti),('inf',-rooti%p)]
branches=[branch(*v)for v in labels]
def evmon(m,vals):
 ans=one
 for exponent,val in zip(m,vals):ans=mul(ans,power(val,exponent))
 return ans
jets=[[evmon(mon6[c],vals)for c in quotcols]for vals in branches]
conditions=[[jets[j][col][n]for col in range(33)]for j in range(1,6)for n in range(5)]
basis,jpiv=kernel(conditions,33)
assert len(jpiv)==25 and len(basis)==8

# Ordinary marked point: first four canonical jets are independent.
a,b,q,t=branches[0]
J=add(add(scale(mul(a,a),2*A),scale(mul(a,q),D)),scale(mul(b,b),-2*B))
canonical=[mul(m,recip(J))for m in (one,a,b,q)]
wronskian=det([[f[n]for f in canonical]for n in range(4)])
assert wronskian

out={
 'prime':p,'specialization':{'A':A,'B':B,'C':C,'D':D,'E':E,'T':T},
 'chart_points':[{'kind':kind,'root':root}for kind,root in labels],
 'degree6_monomial_count':len(mon6),'ideal_rank':len(ipiv),'quotient_dimension':len(quotcols),
 'quotient_monomials':[mon6[c]for c in quotcols],
 'jet_condition_rank':len(jpiv),'compact_RR_dimension':len(basis),
 'condition_pivot_columns':jpiv,'RR_kernel_rows':basis,
 'ordinary_point_canonical_jet_determinant':wronskian,
 'basis_differentials':'sum row[i]*monomial[i] / q^5 times canonical residue generator',
 'status':'exact generic-pivot witness for complete compact rank8 RR basis; no primitive/GM coefficients claimed',
}
Path(__file__).with_name('rr-basis-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in ('prime','ideal_rank','quotient_dimension','jet_condition_rank','compact_RR_dimension','ordinary_point_canonical_jet_determinant','status')},indent=2))
