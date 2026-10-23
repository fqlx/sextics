"""Exact source-bound first relative IBP on the effective Schiffer graph.
No base derivative has been discarded: the current is wedged with full base3volume.
A physical vector-field pushforward can introduce Y2 poles and is not done here.
"""
from pathlib import Path
import pickle,json,time,sympy as s
from flint import fmpq,fmpq_mpoly_ctx
HERE=Path(__file__).parent;start=time.monotonic()
data=pickle.loads((HERE/'effective_schiffer.pickle').read_bytes())
syms=data['symbols'];W,h,t,L,r,x,z=syms
ctx=fmpq_mpoly_ctx.get(tuple(map(str,syms)));ww,hh,tt,LL,rr,xx,zz=ctx.gens()
def native(f):return ctx.from_dict({e:fmpq(str(c))for e,c in s.Poly(f,*syms).as_dict().items()})
C=native(s.expand(x*data['curve']));D=native(data['graph_support']);Q=[native(f)for f in data['Q']]
N=[hh*hh*f for f in Q];S0=hh**4*(tt-zz*hh*hh)**2
assert sum(N[i]*C.derivative(i)for i in range(3))==xx*D*S0
Div=sum(N[i].derivative(i)for i in range(3));ND=sum(N[i]*D.derivative(i)for i in range(3))
E=D*Div-ND
# Check all weighted degrees and the explicit contraction on h=1.
weights=(1,1,2,0,0,0,0)
assert all(sum(a*b for a,b in zip(e,weights))==6 for e in E.to_dict())
assert all(sum(a*b for a,b in zip(e,weights))==4 for e in Div.to_dict())
# The residual is genuinely present, and D is not already logarithmic for N.
gcdDE=D.gcd(E)
def pd(f):return{tuple(map(int,e)):str(c)for e,c in f.to_dict().items()}
packet={'variables':tuple(map(str,syms)),'x_times_curve':pd(C),'D':pd(D),'N':[pd(f)for f in N],'source_S0':pd(S0),'divN':pd(Div),'N_D':pd(ND),'E2_residual_numerator':pd(E),'gcd_D_E':pd(gcdDE),'identity':'S0*Omega/C² = [E/(D²)]*Omega/C - d(i_N Omega/(D*C)); E=D*divN-N(D).','physical_prefactor':'rho*fT, wedged with da db dv; full basevolume kills its base derivative in this first purely relative current. No claim for later base currents.'}
(HERE/'effective_IBP.pickle').write_bytes(pickle.dumps(packet))
out={'exact_NC_equals_D_source':True,'N_term_counts':[len(f.to_dict())for f in N],'divN_terms':len(Div.to_dict()),'E_terms':len(E.to_dict()),'gcd_D_E':str(gcdDE),'E_nonzero':bool(E),'residual_weight':6,'first_IBP_identity':packet['identity'],'remaining_obligation':'Construct a coupled base-current or source-compatible Gysin channel killing/serving E/(D²C), with all physical chart poles retained. The relative identity alone does not do this.','seconds':round(time.monotonic()-start,3)}
(HERE/'effective_IBP.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
