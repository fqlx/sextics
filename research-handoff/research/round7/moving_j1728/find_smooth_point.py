from pathlib import Path
import pickle,json
P=pickle.load(open(Path(__file__).parent/'physical_model.pickle','rb'))
q,h=[P['symbols'][n] for n in ['q','h']]
vals=[P['coefficients'][n].subs({q:1,h:4}) for n in ['a1','a0','b2','b1','b0']]
def det3(M,p):
 return sum((1 if j%2==0 else -1)*M[0][j]*(M[1][(j+1)%3]*M[2][(j+2)%3]-M[1][(j+2)%3]*M[2][(j+1)%3])*(1 if j%2==0 else -1) for j in range(3))%p
# cyclic determinant expansion, all three signs are already captured cyclically.
def det(M,p):return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))%p
for p in [101,103,107,109,127]:
 if any(int(z.q)%p==0 for z in vals):continue
 a1,a0,b2,b1,b0=[int(z.p)*pow(int(z.q),-1,p)%p for z in vals]
 points=[]
 for sl in range(1,p):
  sl2,sl3=sl*sl%p,sl**3%p
  for ti in range(p):
   c2=(3*sl2*ti+a1*sl+b2)%p;c1=(3*sl*ti*ti+a1*ti+a0*sl+b1)%p;c0=(ti**3+a0*ti+b0)%p
   if not c1 or not c2:continue
   v2=4*sl3*pow(c1,-1,p)%p
   vi=-sl3*(v2+3)*pow(c2,-1,p)%p
   if vi*vi%p!=v2 or not vi or v2 in [1,pow(2,-1,p)]:continue
   if (vi**3*c0-2*sl3*(vi**4-1))%p:continue
   J=[[(vi*(6*sl*ti+a1)+3*sl2*(v2+3))%p,vi*3*sl2%p,(c2+2*sl3*vi)%p],[(v2*(3*ti*ti+a0)-12*sl2)%p,v2*(6*sl*ti+a1)%p,2*vi*c1%p],[-6*sl2*(vi**4-1)%p,vi**3*(3*ti*ti+a0)%p,(3*v2*c0-8*sl3*vi**3)%p]]
   dj=det(J,p)
   points.append(dict(s=sl,t=ti,v=vi,jacobian_determinant=dj,twist_s_over_v=sl*pow(vi,-1,p)%p))
 good=[pt for pt in points if pt['jacobian_determinant']]
 print('p',p,'points',len(points),'smooth',len(good),flush=True)
 if good:
  answer=dict(prime=p,base=dict(q=1,h=4),coefficients=dict(zip(['a1','a0','b2','b1','b0'],[a1,a0,b2,b1,b0])),points=points,conclusion='A nonsingular Fp point lifts over Zp by Hensel; the 3-equation model has a component etale and generically finite dominant over physical(q,h). Smoothness exclusions s*v*(v²−1)*(2v²−1) were checked.')
  (Path(__file__).parent/'smooth_point.json').write_text(json.dumps(answer,indent=2));break
