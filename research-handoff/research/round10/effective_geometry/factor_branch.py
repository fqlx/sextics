from pathlib import Path
import pickle,sympy as sp,json,time
from flint import fmpq,fmpq_mpoly_ctx
start=time.time();here=Path(__file__).parent
p=pickle.load(open('/workspace/research/round9/abel_prym/effective_schiffer.pickle','rb'))
_,_,_,l,r,x,z=p['symbols'];ctx=fmpq_mpoly_ctx.get(('L','r','x','z'));L,R,X,Z=ctx.gens()
def native(f):return ctx.from_dict({tuple(map(int,e)):fmpq(str(c))for e,c in sp.Poly(f,l,r,x,z).terms()})
N0=native(p['N0']);N1=native(p['N1']);B=X*L*N0**3+X*R*N1*N0**2+N1**3
D=fmpq(25,49)*X*N0*(N0+N1)**2-4*B
out={}
for name,F in [('B_numerator',B),('Delta_numerator',D)]:
 print('FACTOR_START',name,len(F),time.time()-start,flush=True)
 fac=F.factor();factors=[]
 for f,m in fac[1]:
  factors.append({'polynomial':str(f),'exponent':int(m),'degrees':list(map(int,f.degrees())),'terms':len(f)})
 out[name]={'content':str(fac[0]),'factors':factors}
 print('FACTOR_DONE',name,[(f['degrees'],f['exponent'],f['terms'])for f in factors],time.time()-start,flush=True)
(here/'factor_branch.json').write_text(json.dumps(out,indent=2)+'\n')
print('DONE',time.time()-start,flush=True)
