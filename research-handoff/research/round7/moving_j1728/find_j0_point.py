from find_smooth_point import P,vals,det
from pathlib import Path
import json
for p in [103,109,127,139,151]:
 if any(int(z.q)%p==0 for z in vals):continue
 roots=[ell for ell in range(p)if (ell*ell-ell+1)%p==0]
 for ell in roots:
  a1,a0,b2,b1,b0=[int(z.p)*pow(int(z.q),-1,p)%p for z in vals];points=[]
  for sl in range(1,p):
   sl2,sl3=sl*sl%p,sl**3%p
   for ti in range(p):
    c2=(3*sl2*ti+a1*sl+b2)%p;c1=(3*sl*ti*ti+a1*ti+a0*sl+b1)%p;c0=(ti**3+a0*ti+b0)%p
    den=(c1-(8*ell-4)*sl3)%p
    if not den or not c2:continue
    v2=8*ell*sl3*pow(den,-1,p)%p;vi=-sl3*(v2+1+4*ell)*pow(c2,-1,p)%p
    if vi*vi%p!=v2 or not vi or v2 in [1,ell]:continue
    if (vi**3*c0+4*sl3*(v2+1)*((ell-1)*v2+ell))%p:continue
    T=(8*ell-4)*v2+8*ell;R=(ell-1)*v2+ell
    J=[[(vi*(6*sl*ti+a1)+3*sl2*(v2+1+4*ell))%p,3*vi*sl2%p,(c2+2*sl3*vi)%p],[(v2*(3*ti*ti+a0)-3*sl2*T)%p,v2*(6*sl*ti+a1)%p,(2*vi*c1-2*vi*sl3*(8*ell-4))%p],[12*sl2*(v2+1)*R%p,vi**3*(3*ti*ti+a0)%p,(3*v2*c0+8*sl3*vi*(2*(ell-1)*v2+2*ell-1))%p]]
    points.append(dict(s=sl,t=ti,v=vi,jacobian_determinant=det(J,p),twist=sl*pow(vi,-1,p)%p))
  print('j0 p',p,'ell',ell,'points',len(points),'smooth',sum(bool(r['jacobian_determinant'])for r in points),flush=True)
  if any(r['jacobian_determinant']for r in points):
   ans=dict(prime=p,ell=ell,base=dict(q=1,h=4),points=points,conclusion='smooth point proves an etale generically finite dominant component over physical(q,h) over Q(ell), ell²-ell+1=0')
   (Path(__file__).parent/'j0_smooth_point.json').write_text(json.dumps(ans,indent=2));raise SystemExit
