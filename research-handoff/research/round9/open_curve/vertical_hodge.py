"""Compact Higgs extension along the universal Prym-isoperiodic flow."""
from pathlib import Path
import pickle,json,time
from flint import fmpq_mpoly_ctx,fmpq_mpoly,fmpq
HERE=Path(__file__).parent;start=time.monotonic()
# Reuse only the checked native rational arithmetic, without executing its solver.
source=(HERE/'native_solve.py').read_text().split('zero=RF(0)')[0]
exec(compile(source,'native_rf_definition','exec'))
ctx=fmpq_mpoly_ctx.get(('L','r','x','s'));L,r,x,s=ctx.gens();c=fmpq(5,7)
zero=RF(0)
def read(v):return RF(ctx.from_dict({e:fmpq(a)for e,a in v['numerator'].items()}),ctx.from_dict({e:fmpq(a)for e,a in v['denominator'].items()}))
d=pickle.loads((HERE/'boundary_native.pickle').read_bytes())
flow=[x*((c*c-10*r)*L+4*r*r),x*r*(c*c-5*r)-18*L+9*r,-x*((c*c+5*r)*x+27)]
result=[];summary=[]
for j in range(2):
 val=sum((read(d['connection_boundary'][name][j][2])*RF(v)for name,v in zip(['L','r','x'],flow)),zero)
 result.append(val.payload())
 summary.append({'numerator':str(val.n),'denominator':str(val.d),'numerator_terms':len(val.n.to_dict()),'denominator_factors':[(str(f),int(e))for f,e in val.d.factor()[1]]})
G=L*x+r*x*s+s**3
Delta=RF(c*c*x*(s+1)**2-4*G,x)
K=RF(r*x*(5*s+4)+3*s*(2*s+3),x)
ES=[read(d['connection_boundary']['s'][j][2])for j in range(2)]
compact=[RF(x)*K*ES[0]+RF(-2*c)/(RF(7)*Delta),RF(x)*K*ES[1]+RF(c*c*(s+1))/(RF(7)*Delta)]
for j in range(2):assert not(read(result[j])-compact[j]).n
# Universal quadratic-algebra simplification of the sheetwise theta pairing.
import sympy as sy
u,aa,bb,kk,nu0,xx0,cc=sy.symbols('u A B K d x c')
DD=aa*aa-4*bb
EE0=(nu0/xx0+kk)*aa/(7*bb*DD)-2*cc/(7*DD)
EE1=-(nu0/xx0+kk)*2/(7*DD)+cc*aa/(7*DD)
check=(-aa-u)*EE0-EE1-(nu0/xx0+kk+cc*u)/(7*u*(2*u+aa))
num=sy.cancel(check).as_numer_denom()[0]
assert sy.rem(num,u*u+aa*u+bb,u)==0
(HERE/'vertical_hodge.pickle').write_bytes(pickle.dumps({'variables':('L','r','x','s'),'flow':[str(f)for f in flow],'E_eta_flow':result,'compact_identities_exact':True,'compact_rule':'E_delta=x*K*E_s+c*(-2,A)/(7*Delta); E_s=(A,-2B)/(7*x*B*Delta),K=r(5s+4)+3s(2s+3)/x'}))
(HERE/'vertical_hodge.json').write_text(json.dumps({'flow':list(map(str,flow)),'E_eta_flow':summary,'compact_identities_exact':True,'sheetwise_theta_contraction_exact':True,'compact_rule':'For moving s, f.E=[delta(s)/x+K+c*u]/[7*w*(2u+A)], f=w²*(-A-u,-1), u=w³.','scope':'Exact contraction along the universal Prym-isoperiodic flow at fixed marked s. Add E_s*delta(s) for a moving graph.','seconds':time.monotonic()-start},indent=2)+'\n')
print((HERE/'vertical_hodge.json').read_text())
