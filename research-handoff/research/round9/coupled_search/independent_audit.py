"""Independent frame/weight/source audit of the coupled cyclic evaluator.

In particular the source is reduced afresh in the weighted Jacobian ring,
rather than reconstructed using the source rows of the exported connection.
"""
from pathlib import Path
import importlib.util,json,pickle,sympy as s
from flint import nmod_mat
HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('candidate',HERE/'search.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
raw=pickle.loads((HERE.parent/'cyclic_full/actual_fast.pickle').read_bytes())
W,h,t,L,r,x=raw['symbols'];variables=(W,h,t);C=raw['curve'];base=(L,r,x)
def mon(e):return W**e[0]*h**e[1]*t**e[2]
rows=[(i,j,k)for i in range(9)for j in range(9)for k in range(5)if i+j+2*k==8 and i%3==0]
lab=[(i,e)for i,wt,ch in [(0,3,1),(1,3,0),(2,4,0)]for e in [(a,b,c)for a in range(wt+1)for b in range(wt+1)for c in range(wt//2+1)if a+b+2*c==wt and a%3==ch]]
J=s.Matrix([[s.Poly(s.diff(C,variables[i])*mon(e),*variables).coeff_monomial(mon(rr))for i,e in lab]for rr in rows])
eta=raw['eta'][0]
J=J.row_join(s.Matrix([int(mon(rr)==eta)for rr in rows]))
div=s.Matrix([[s.Poly(s.diff(mon(e),variables[i]),*variables).coeff_monomial(z)for i,e in lab]for z in (h*h,t)])

# Exact logarithmic factors, independent of sampling and of the model's Jets.
a,b,v=s.symbols('a b v');S=1+a**6+b**6;E=1+a*v;B=b*E;R=s.Rational(5,7)*(a*b+v*b**3);A=3*S-B*R
M=A/(3*S);fT=3*a**3*S/(2*B**3*A)
canonical_log=[3/a+s.Rational(13,3)*s.diff(A,a)/A-s.Rational(4,3)*s.diff(S,a)/S-4*s.diff(E,a)/E,
               -5/b+s.Rational(13,3)*s.diff(A,b)/A-s.Rational(4,3)*s.diff(S,b)/S-4*s.diff(E,b)/E,
               s.Rational(13,3)*s.diff(A,v)/A-s.Rational(4,3)*s.diff(S,v)/S-4*s.diff(E,v)/E]
physical_log=[s.cancel(s.diff(fT,z)/fT+s.diff(M,z)/(3*M))for z in (a,b,v)]
expected=[3/a+s.Rational(2,3)*s.diff(S,a)/S-3*s.diff(E,a)/E-s.Rational(2,3)*s.diff(A,a)/A,
          -3/b+s.Rational(2,3)*s.diff(S,b)/S-3*s.diff(E,b)/E-s.Rational(2,3)*s.diff(A,b)/A,
          s.Rational(2,3)*s.diff(S,v)/S-3*s.diff(E,v)/E-s.Rational(2,3)*s.diff(A,v)/A]
assert all(s.cancel(p-q)==0 for p,q in zip(physical_log,expected))
samples=[]
for prime in [1000003,1000033,101]:
    model=mod.Model(prime)
    def red(q):
        n,d=s.fraction(s.cancel(q));return int(n)%prime*pow(int(d),-1,prime)%prime
    for point in [(1,2,3),(2,1,3),(2,3,1),(3,4,2)]:
        try:pt=model.point(point)
        except (ValueError,ZeroDivisionError):continue
        sub=dict(zip(base,pt['pars']));AA=nmod_mat([[red(z.subs(sub))for z in J.row(i)]for i in range(J.rows)],prime)
        zz=pt['z'].x
        P=s.Poly(h**4*(t-zz*h*h)**2,*variables)
        rhs=nmod_mat([[red(P.coeff_monomial(mon(rr)))]for rr in rows],prime)
        sol=AA.solve(rhs)
        out=[sum(red(div[i,k])*int(sol[k,0])for k in range(len(lab)))%prime for i in range(2)]+[int(sol[len(lab),0])]
        assert out==pt['rhs'],(prime,point,out,pt['rhs'])
        ps=dict(zip((a,b,v),point))
        assert [red(z.subs(ps))for z in physical_log]==pt['logF']
        D,dD=model.polys['Delta47'].eval(point,True)
        cl=[(red(z.subs(ps))-dD[i]*pow(D,-1,prime))%prime for i,z in enumerate(canonical_log)]
        assert cl==pt['logH']
        # Transform a physical coordinate current into canonical coordinates.
        # Piola: sum_j V_j(J[j,l])=partial_l(log det J).  Thus the
        # two logarithmic/current formulas agree; verify all connection terms.
        for ell in range(3):
            for comp in range(3):
                got=[sum(pt['J'][j][ell]*pt['N'][j][comp][i]for j in range(3))%prime for i in range(3)]
                label=[('physical',ell,comp,0,(0,0,0))]
                got[comp]=(got[comp]+pt['logF'][ell])%prime
                assert got==[row[0]for row in mod.sample_columns(pt,label,prime)]
        samples.append(dict(prime=prime,point=point,source=out,source_direct_Jacobian_reduction=True,frame_and_weight=True))
ans=dict(samples=samples,exact_cubic_charge_weight=True,
         canonical_density='H=rho*fT/detJ',physical_density='rho*fT',
         transpose='connection rows are basis derivatives; coefficient vectors use N^T',
         source_checked_without_source_connection_rows=True,
         source_pole2_numerator='h^4*(t-z*h^2)^2; divide by C^2',
         canonical_physical_frame_equivalence='Piola plus chain rule; same rhs',
         scope='Evaluator audit, no current solution and no enlarged search-space claim.')
(HERE/'independent_audit.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps(ans,indent=2))
