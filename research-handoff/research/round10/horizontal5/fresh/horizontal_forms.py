"""Exact horizontal residue forms, including the physical rho-density twist.

Uses the previously audited residue matrix. It does not recompute the rank5
proper connection or assert that an exact residue form solves its source.
"""
from pathlib import Path
from itertools import combinations
import sympy as s
import pickle,json

HERE=Path(__file__).parent
A,B,m,F,f,g=s.symbols('A B m F f g')
coords=(A,B,m,F,f,g)
def clean(form):
    out={}
    for key,value in form.items():
        value=s.cancel(value)
        if value:
            out[key]=value
    return out
def add(*forms):
    out={}
    for form in forms:
        for key,value in form.items():out[key]=out.get(key,0)+value
    return clean(out)
def scale(a,form):return clean({key:a*value for key,value in form.items()})
def wedge(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items():
            if set(i)&set(j):continue
            key=i+j
            sign=(-1)**sum(x>y for x in i for y in j)
            key=tuple(sorted(key))
            out[key]=out.get(key,0)+sign*x*y
    return clean(out)
def derivative(form):
    out={}
    for key,value in form.items():
        for i,x in enumerate(coords):
            if i in key:continue
            target=tuple(sorted((i,)+key))
            sign=(-1)**sum(i>j for j in key)
            out[target]=out.get(target,0)+sign*s.diff(value,x)
    return clean(out)
def df(expr):return derivative({():expr})
dA,dB,dm,dF,ddf,ddg=[df(x) for x in coords]
kappa=scale(1/(3*m),dm)
twist=add(kappa,scale(1/F,dF))
D=A*A-4*B
RA=s.Matrix([[-A/(3*D),4/(3*D)],[2*B/(3*D),-2*A/(3*D)]])
RB=s.Matrix([[(10*B-2*A*A)/(3*B*D),-2*A/(3*B*D)],[-A/(3*D),4/(3*D)]])
R=[[add(scale(RA[i,j],dA),scale(RB[i,j],dB)) for j in range(2)] for i in range(2)]
def horizontal(gamma):
    return [add(derivative(gamma[i]),wedge(twist,gamma[i]),
                *[wedge(R[j][i],gamma[j]) for j in range(2)])
            for i in range(2)]
def covariant(form):
    return [add(derivative(form[i]),wedge(twist,form[i]),
                *[wedge(R[j][i],form[j]) for j in range(2)])
            for i in range(2)]

# On the degree-six graph, d(rho*w) and d(rho*w^4) have the following
# sigma-coordinate one-forms, divided by rho.  The + signs of kappa are
# forced by the ordinary product rule, not chosen to fit a connection.
Hw=[add(dB,scale(6*B,kappa)),add(dA,scale(3*A,kappa))]
Hw4=[add(scale(-4*B,dA),scale(-3*A*B,kappa)),
     add(scale(4,dB),scale(-4*A,dA),scale(3*(2*B-A*A),kappa))]
Tw=[6*B,3*A]
Tw4=[-3*A*B,3*(2*B-A*A)]
families={}
for name,H,T in [('w',Hw,Tw),('w4',Hw4,Tw4)]:
    simple=[scale(1/F,wedge(h,ddg)) for h in H]
    general=[scale(1/F,add(scale(f,wedge(H[i],ddg)),
                          scale(T[i],wedge(ddf,ddg)))) for i in range(2)]
    assert horizontal(simple)==[{},{}]
    assert horizontal(general)==[{},{}]
    potential=[scale(f*T[i]/F,ddg) for i in range(2)]
    assert covariant(potential)==general
    families[name]={'simple':simple,'general':general,'potential':potential}

# The uncharged finite-cover isomorphism and its exact gauge identity.
T=s.Matrix([[6*B,-3*A*B],[3*A,3*(2*B-A*A)]])
assert s.factor(T.det())==-9*B*D
lA=s.Matrix([[-A/(3*D),-2/(3*D)],
             [8*B/(3*D),4*A/(3*D)]])
lB=s.Matrix([[(A*A-2*B)/(3*B*D),A/(3*B*D)],
             [-4*A/(3*D),-8/(3*D)]])
for x,RR,SS in [(A,RA,lA),(B,RB,lB)]:
    assert all(s.cancel(z)==0 for z in T.diff(x)+RR.T*T-T*SS.T)

def encode(form):
    return {','.join(str(coords[i]) for i in key):str(value) for key,value in form.items()}
eff=pickle.load(open('/workspace/research/round9/abel_prym/effective_schiffer.pickle','rb'))
packet=dict(symbols=coords,residue_matrices={'dA':RA,'dB':RB},
            kappa=kappa,full_density_twist=twist,T=T,
            exact_families=families,effective_schiffer=eff,
            physical_substitution=dict(
                variables=('a','b','v'),c='5/7',E='1+a*v',
                Bphys='b*(1+a*v)',S='1+a^6+b^6',
                Rphys='(5/7)*(a*b+v*b^3)',Qphys='(5/7)*a*b*v',
                Aphys='3*S-Bphys*Rphys',Hphys='27*(1+v^6)*S^2-9*Qphys*Rphys*S+2*Rphys^3',
                Jphys='3*S*Qphys-Rphys^2',
                L='Hphys/(3*Aphys^2)',r='Jphys/(Bphys*Aphys)',
                x='3*Bphys^3/Aphys',z='Bphys*Rphys/Aphys',
                s_eff='N1(L,r,x,z)/N0(L,r,x,z)',
                m='Aphys/(3*S)',F='3*a^3*S/(2*Bphys^3*Aphys)',
                A='(5/7)*(1+s_eff)',B='L+r*s_eff+s_eff^3/x'),
            physical_vector_rule='i_Z(da db dv)=gamma: Z=(gamma_bv,-gamma_av,gamma_ab)',
            finite_cover='w^6+A*w^3+B=0; u=w^3',
            residue_map='alpha=-(gamma0+u*gamma1)/(3*w^2*(2*u+A))',
            full_twist='dlog(rho*F)=dm/(3*m)+dF/F; rho^3=m',
            source_rule='These supply residue-closed currents only; proper extension/source matching remains to be computed.')
(HERE/'horizontal_forms.pickle').write_bytes(pickle.dumps(packet))
ans=dict(all_exact_checks_pass=True,finite_cover_map=packet['residue_map'],
         residue_closedness='d gamma + R^T wedge gamma=0',
         physical_closedness='d Z + (Rphys^T + dlog(rho*fT) I) wedge Z=0',
         gauge_determinant=str(s.factor(T.det())),
         simple_w=[encode(q) for q in families['w']['simple']],
         simple_w4=[encode(q) for q in families['w4']['simple']],
         general_families={name:[encode(q) for q in value['general']] for name,value in families.items()},
         physical_small_candidates='Set (f,g)=(1,a),(1,b),(1,v); or (f,g)=(a,b),(a,v),(b,v), in each of the two families. All normalized current coefficients are rational after substituting m,F,A,B.',
         exactness='Residues are d(rho*w*f) wedge dg or d(rho*w^4*f) wedge dg, divided by the physical rho-density convention. They are de Rham-exact and do not by themselves establish a new H20 class.',
         scope='Exact horizontal preconditioners and finite-cover de Rham identification; no proper source primitive or certificate.')
(HERE/'horizontal_forms.json').write_text(json.dumps(ans,indent=2)+'\n')
print(json.dumps({k:v for k,v in ans.items() if k not in ('general_families','simple_w','simple_w4')},indent=2),flush=True)
