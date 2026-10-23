"""Find a reproducible transverse physical basepoint off all curve boundaries.

A rank-two Jacobian minor and unit discriminants at a good finite prime give
a smooth mixed-characteristic point and hence a characteristic-zero common-
zero component with the required open local conditions. No global H20 follows.
"""
from pathlib import Path
from fractions import Fraction
import pickle,json
import numpy as np
import sympy as sp
HERE=Path(__file__).parent
data=pickle.load(open('/workspace/research/round9/abel_prym/effective_physical.pickle','rb'))['T_effective_canonical']
p=101
def mod(c):
    c=Fraction(c);return c.numerator%p*pow(c.denominator%p,-1,p)%p
polys={key:{e:mod(c) for e,c in poly.items()} for key,poly in data.items()}
def value(poly,point):
    return sum(c*pow(point[0],e[0],p)*pow(point[1],e[1],p)*pow(point[2],e[2],p) for e,c in poly.items())%p
def gradient(poly,point):
    out=[]
    for j in range(3):
        q={tuple(k-(i==j) for i,k in enumerate(e)):c*e[j]%p for e,c in poly.items() if e[j]}
        out.append(value(q,point))
    return out
inv=lambda x:pow(int(x)%p,-1,p)
c=5*inv(7)%p
deg=pickle.load(open('/workspace/research/round10/effective_geometry/degeneracy.pickle','rb'))
l,r,x,_,_=deg['symbols']
d2=sp.Poly(deg['D2'],l,r,x).as_dict()
def frame(point):
    a,b,v=point
    E=(1+a*v)%p;BP=b*E%p;S=(1+pow(a,6,p)+pow(b,6,p))%p
    R=c*(a*b+v*pow(b,3,p))%p;Q=c*a*b*v%p
    AP=(3*S-BP*R)%p
    if not all([a,b,E,BP,S,AP]):return None
    H=(27*(1+pow(v,6,p))*S*S-9*Q*R*S+2*pow(R,3,p))%p
    J=(3*S*Q-R*R)%p
    L=H*inv(3*AP*AP)%p;rr=J*inv(BP*AP)%p;xx=3*pow(BP,3,p)*inv(AP)%p
    D1=(27*L*L+4*pow(rr,3,p)*xx)%p
    D2=sum(mod(str(co))*pow(L,e[0],p)*pow(rr,e[1],p)*pow(xx,e[2],p) for e,co in d2.items())%p
    if not all([xx,D1,D2]):return None
    return dict(L=L,r=rr,x=xx,z=BP*R*inv(AP)%p,D1=D1,D2=D2,
                AP=AP,BP=BP,S=S,E=E)

grid=np.arange(1,p,dtype=np.int64)
aa,bb=np.meshgrid(grid,grid,indexing='ij')
ap=[np.ones_like(aa)];bp=[np.ones_like(bb)]
for k in range(1,21):ap.append(ap[-1]*aa%p);bp.append(bp[-1]*bb%p)
found=None
for v in range(1,p):
    vals=[]
    for poly in polys.values():
        accum=np.zeros_like(aa)
        for e,co in poly.items():accum=(accum+co*pow(v,e[2],p)*ap[e[0]]*bp[e[1]])%p
        vals.append(accum)
    for ai,bi in np.argwhere((vals[0]==0)&(vals[1]==0)):
        point=(int(grid[ai]),int(grid[bi]),v)
        fr=frame(point)
        if fr is None:continue
        gn=gradient(polys['num'],point);gd=gradient(polys['den'],point)
        minors={(i,j):(gn[i]*gd[j]-gn[j]*gd[i])%p for i in range(3) for j in range(i+1,3)}
        nonzero={str(key):val for key,val in minors.items() if val}
        if not nonzero:continue
        found=dict(point=point,num_value=value(polys['num'],point),den_value=value(polys['den'],point),
                   num_gradient=gn,den_gradient=gd,nonzero_Jacobian_minors=nonzero,canonical_frame=fr)
        break
    if found:break
assert found is not None
ans=dict(prime=p,physical_basepoint=found,
         characteristic_zero_inference='Fix the third coordinate complementary to a nonzero 2x2 minor. The two polynomial equations then have an etale local zero over Z_(101), and all excluded factors are units. Hensel/etale lifting gives a characteristic-zero common-zero component with transverse N0,N1 and smooth canonical curve.',
         caveat='This proves nonemptiness of the good local cone mechanism on a characteristic-zero component; it does not establish global smoothness, eigensheaf transitions, H20 extension, or serving image.')
(HERE/'transverse_point.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps(ans,indent=2),flush=True)
