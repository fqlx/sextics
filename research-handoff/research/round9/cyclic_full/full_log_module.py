"""Exact full product-log module and polynomial connection contractions."""
from pathlib import Path
import sympy as s,pickle,json,importlib.util,itertools,time
root=Path(__file__).parent;start=time.monotonic()
spec=importlib.util.spec_from_file_location('native_rf_log',root/'theta_frame.py');rf=importlib.util.module_from_spec(spec);spec.loader.exec_module(rf)
good=pickle.loads((root/'global_eta_complete.pickle').read_bytes());hi=pickle.loads((root/'global_eta_high_input.pickle').read_bytes());L,r,x=s.symbols('L r x');pars=(L,r,x)
D=hi['D'];fs=s.factor_list(D)[1];D1=[f for f,e in fs if len(s.Poly(f,*pars).terms())==2][0];D2=s.cancel(D/(x*D1))
text=(root/'full_log_module.log').read_text();assert text.startswith('SIZE\n4\n') and '?'not in text
gens=[]
for j in range(1,5):
    gen=[s.sympify(text.split('COEFF '+str(j)+' '+str(i)+'\n')[1].split('\n')[0].replace('^','**'))for i in range(1,7)]
    for div,q in [(D1,gen[3]),(D2,gen[4]),(x,gen[5])]:
        assert s.expand(sum(s.diff(div,z)*v for z,v in zip(pars,gen[:3]))-q*div)==0
    gens.append(gen)
parse=lambda a:rf.RF(rf.fmpq_mpoly(a['numerator'],rf.ctx),rf.fmpq_mpoly(a['denominator'],rf.ctx))
N={name:[[parse(v)for v in row]for row in mat]for name,mat in good['connection'].items()}
contractions=[];denoms=[]
for gen in gens:
    mat=[[sum((rf.convert(gen[k])*N[str(pars[k])][i][j]for k in range(3)),rf.zero)for j in range(3)]for i in range(3)]
    facts=[]
    for row in mat:
        for e in row:
            if not e.d.is_constant():facts.append(str(e.d))
    contractions.append([[e.json()for e in row]for row in mat]);denoms.append(sorted(set(facts)))
ratios={','.join(map(str,inds)):str(s.factor(s.det(s.Matrix.hstack(*[s.Matrix(gens[i][:3])for i in inds]))/D))for inds in itertools.combinations(range(4),3)}
assert ratios['0,1,2']=='-120050'
assert all(e==1 for f,e in s.factor_list(D)[1])
relation=[s.Rational(2,25)*(-96040*L*r+24500*L+38416*r*r-13720*r-1625),
          (-34300*L+38416*r*r-13720*r-1625)/5,
          -s.Rational(3,25)*(-245*L+98*r-10)]
assert all(s.expand(sum(relation[j]*gens[j][i]for j in range(3))-gens[3][i])==0 for i in range(6))
out=dict(symbols=pars,D1=D1,D2=D2,fields=[g[:3]for g in gens],log_derivatives=[g[3:]for g in gens],
         divergences=[s.expand(sum(s.diff(v,z)for v,z in zip(g[:3],pars)))for g in gens],
         connection_contractions=contractions,nonconstant_contraction_denominators=denoms,
         determinant_ratios=ratios,
         basis_indices=[0,1,2],basis_determinant='-120050*x*D1*D2',log_divisor_reduced=True,
         fourth_generator_relation=list(map(str,relation)),
         completeness='First three fields are a complete free basis of Der(log(xD1D2)) by exact logarithmic tangency and the Saito determinant criterion. The fourth Singular generator is an explicitly verified polynomial combination.',
         source_convention='For a current f*V, use V(f)+(div(V)+V(log H))*f+N(V)^T*f, retaining the physical density H.',
         scope='Exact tangent module and connection contractions, not a target primitive.',seconds=time.monotonic()-start)
(root/'full_log_module.pickle').write_bytes(pickle.dumps(out))
js={k:v for k,v in out.items()if k not in ('symbols','D1','D2','fields','log_derivatives','divergences')};js.update(D1=str(D1),D2=str(D2),fields=[[str(v)for v in g[:3]]for g in gens],log_derivatives=[[str(v)for v in g[3:]]for g in gens],divergences=list(map(str,out['divergences'])))
(root/'full_log_module.json').write_text(json.dumps(js,indent=2)+'\n');print(json.dumps({k:v for k,v in js.items()if k!='connection_contractions'},indent=2))
