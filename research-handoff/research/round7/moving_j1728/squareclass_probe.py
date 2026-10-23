from pathlib import Path
import pickle,json
P=pickle.load(open(Path(__file__).parent/'physical_model.pickle','rb'))
q,h=[P['symbols'][n] for n in ['q','h']]
p=107
invs={a:pow(a,-1,p)for a in range(1,p)}
coeffs={n:__import__('sympy').Poly(P['coefficients'][n],q,h).terms()for n in ['a1','a0','b2','b1','b0']}
def evterms(terms,qv,hv):return sum((int(c.p)*invs[int(c.q)%p]%p)*pow(qv,m[0],p)*pow(hv,m[1],p)for m,c in terms)%p
def chi(a):return 0 if not a%p else (1 if pow(a%p,(p-1)//2,p)==1 else -1)
rows=[]
for qv in range(1,9):
 for hv in range(3,9):
  a1,a0,b2,b1,b0=[evterms(coeffs[n],qv,hv) for n in coeffs]
  for sl in range(1,p):
   sl2,sl3=sl*sl%p,sl**3%p
   for ti in range(p):
    c2=(3*sl2*ti+a1*sl+b2)%p;c1=(3*sl*ti*ti+a1*ti+a0*sl+b1)%p;c0=(ti**3+a0*ti+b0)%p
    if not c1 or not c2:continue
    v2=4*sl3*invs[c1]%p;vi=-sl3*(v2+3)*invs[c2]%p
    if vi*vi%p!=v2 or not vi or v2 in [1,invs[2]]:continue
    if (vi**3*c0-2*sl3*(vi**4-1))%p:continue
    alpha=sl*invs[vi]%p;fv=(v2-1)*(2*v2-1)%p
    rows.append(dict(q=qv,h=hv,s=sl,t=ti,v=vi,alpha=alpha,chi_alpha=chi(alpha),chi_fv=chi(fv),chi_alpha_over_fv=chi(alpha*invs[fv])))
ans=dict(prime=p,points=rows)
(Path(__file__).parent/'squareclass_probe.json').write_text(json.dumps(ans,indent=2))
print('points',len(rows))
for qv in range(1,9):
 R=[r for r in rows if r['q']==qv];print(qv,'points',len(R),'alpha_signs',sorted(set(r['chi_alpha']for r in R)),'alpha/f(v)_signs',sorted(set(r['chi_alpha_over_fv']for r in R)))
