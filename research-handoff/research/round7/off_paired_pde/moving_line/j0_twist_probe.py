import pickle,json,sympy as S
from pathlib import Path
P=pickle.load(open('/workspace/research/round7/moving_j1728/legendre_model.pickle','rb'))
q,h=[P['symbols'][n]for n in ('q','h')]
p=103;ell=57
coef=[P['coefficients'][n]for n in ('a1','a0','b2','b1','b0')]
points=[]
def cv(z):return int(z.p)*pow(int(z.q),-1,p)%p
for qq in range(1,9):
 for hh in range(3,9):
  if (hh*hh-4)%p==0:continue
  a1,a0,b2,b1,b0=[cv(x.subs({q:qq,h:hh}))for x in coef]
  for sl in range(1,p):
   sl2=sl*sl%p;sl3=sl2*sl%p
   for vi in range(1,p):
    v2=vi*vi%p
    if v2 in (1,ell):continue
    ti=-(vi*(a1*sl+b2)+sl3*(v2+1+4*ell))*pow(3*vi*sl2,-1,p)%p
    c1=(3*sl*ti*ti+a1*ti+a0*sl+b1)%p
    if (v2*c1-sl3*((8*ell-4)*v2+8*ell))%p:continue
    c0=(ti**3+a0*ti+b0)%p
    if (vi**3*c0+4*sl3*(v2+1)*((ell-1)*v2+ell))%p:continue
    w=sl*pow(vi,-1,p)%p;r=(hh*hh-4)%p
    chi=lambda z:1 if pow(z%p,(p-1)//2,p)==1 else -1
    points.append(dict(q=qq,h=hh,s=sl,t=ti,v=vi,alpha=w,chi_alpha=chi(w),chi_alpha_over_r=chi(w)*chi(r)))
rows={qq:sorted({d['chi_alpha_over_r']for d in points if d['q']==qq})for qq in range(1,9)}
out={'prime':p,'ell':ell,'points':points,'chi_w_over_r_by_q':rows,'scope':'finite-field squareclass candidate screen only; components not separated'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print('points',len(points),'q signs',rows)
