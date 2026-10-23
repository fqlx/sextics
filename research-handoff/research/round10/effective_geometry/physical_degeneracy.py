from pathlib import Path
import pickle,sympy as sp,json,time
from flint import fmpq,fmpq_mpoly_ctx
start=time.time();here=Path(__file__).parent
p=pickle.load(open(here/'degeneracy.pickle','rb'));L,r,x,z,s=p['symbols']
print('disc_L_J',sp.factor(sp.discriminant(p['J'],L)),flush=True)
ctx=fmpq_mpoly_ctx.get(('a','b','v'));a,b,v=ctx.gens();c=fmpq(5,7)
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
A=3*S-B*R;H=27*P*S*S-9*Q*R*S+2*R**3;T=3*S*Q-R*R
out={}
for name,poly in [('J',p['J']),('Zlinear',p['common_linear'])]:
 coeff=sp.Poly(poly,L,r,x,z).as_dict();ae=max(0,max(2*i+j+k+l for i,j,k,l in coeff));be=max(0,max(j-3*k-l for i,j,k,l in coeff))
 num=ctx.constant(0)
 for(i,j,k,l),q in coeff.items():num+=fmpq(str(q))*fmpq(3)**(k-i)*H**i*T**j*R**l*A**(ae-2*i-j-k-l)*B**(be-j+3*k+l)
 den=A**ae*B**be;g=num.gcd(den);num//=g;den//=g
 fac=num.factor();out[name]={'num':str(num),'den':str(den),'factors':[{'poly':str(f),'exp':int(m),'degrees':list(map(int,f.degrees())),'terms':len(f)}for f,m in fac[1]]}
 print(name,[(q['degrees'],q['exp'],q['terms'])for q in out[name]['factors']],time.time()-start,flush=True)
(here/'physical_degeneracy.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',time.time()-start,flush=True)
