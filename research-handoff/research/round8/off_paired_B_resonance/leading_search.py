"""Finite rational leading-coefficient search on the invariant s=0 divisor.

Positive output would still require exact reconstruction. Negative output is
only a finite GF(p) ansatz result, not a local/global obstruction.
"""
from pathlib import Path
import argparse,json,time
import sympy as s
from flint import nmod_mpoly_ctx,nmod_mat

HERE=Path(__file__).parent
P=1000003
e,V=s.symbols('eta V')
data=json.loads((HERE/'boundary.json').read_text())
vel=[s.sympify(data[x])for x in ['delta_eta','delta_V']]
mu=s.sympify(data['delta_s_over_s'])
d=5*(1+V**6)*(9*e+14)*(e*V**2-1)
dv=[s.cancel(d*f)for f in vel]
mm=s.cancel(d*mu)

# Independent free-jet check of the cleared operator.
p0,p1,p2,z,z1,z2,dd,dd1,m,m1=s.symbols('p0 p1 p2 z z1 z2 dd dd1 m m1')
delta_w=(p1*z-p0*z1)/(dd*z*z)
delta2_w=(dd*z*(p2*z-p0*z2)-(p1*z-p0*z1)*(dd1*z+2*dd*z1))/(dd**3*z**3)
expr=delta2_w-(s.Rational(8,3)*m/dd+27)*delta_w+(s.Rational(16,9)*m*m/dd**2-s.Rational(4,3)*(m1*dd-m*dd1)/dd**3+36*m/dd+162)*p0/z
c2=9*dd*z*z
c1=-9*dd1*z*z-18*dd*z1*z-(24*m+243*dd)*dd*z*z
c0=18*dd*z1*z1-9*dd*z2*z+9*dd1*z1*z+(24*m+243*dd)*dd*z*z1+(16*m*m*dd-12*(m1*dd-m*dd1)+324*m*dd*dd+1458*dd**3)*z*z
assert s.cancel(9*dd**3*z**3*expr-(c2*p2+c1*p1+c0*p0))==0

ctx=nmod_mpoly_ctx.get(('eta','V'),P)
x,y=ctx.gens()
def cv(f):
    return ctx.from_dict({ex:int(a.p)*pow(int(a.q),-1,P)%P for ex,a in s.Poly(f,e,V).terms()})
DD=cv(d);MV=cv(mm);Dvec=list(map(cv,dv))
def D(f):return Dvec[0]*f.derivative(0)+Dvec[1]*f.derivative(1)

def run(degree,constrained=False):
    start=time.monotonic()
    # A broad but finite natural denominator. All factors are explicit
    # boundary singular/support factors, with the E^4 charge factor retained.
    Z=y*(x+1)**2 if constrained else y*(1+y**6)*(9*x+14)*(x*y*y-1)*(x+1)**4
    factor=(1+y**6)**2*(9*x+14)**2 if constrained else ctx.constant(1)
    DZ=D(Z);D2Z=D(DZ);Dden=D(DD);Dm=D(MV)
    C2=9*DD*Z*Z
    C1=-9*Dden*Z*Z-18*DD*DZ*Z-(24*MV+243*DD)*DD*Z*Z
    C0=(18*DD*DZ*DZ-9*DD*D2Z*Z+9*Dden*DZ*Z
        +(24*MV+243*DD)*DD*Z*DZ
        +(16*MV*MV*DD-12*(Dm*DD-MV*Dden)+324*MV*DD*DD+1458*DD**3)*Z*Z)
    Zsym=V*(e+1)**2 if constrained else V*(1+V**6)*(9*e+14)*(e*V**2-1)*(e+1)**4
    rhs=cv(s.cancel(s.sympify(data['source_times_s'])*9*d**3*Zsym**3))
    mons=[(a,n-a)for n in range(degree+1)for a in range(n+1)]
    columns=[]
    for a,b in mons:
        f=factor*x**a*y**b
        columns.append((C2*D(D(f))+C1*D(f)+C0*f).to_dict())
    target=rhs.to_dict()
    rows=sorted(set(target).union(*(set(c)for c in columns)))
    matrix=nmod_mat([[c.get(row,0)for c in columns]for row in rows],P)
    rank=matrix.rank()
    aug=nmod_mat([[c.get(row,0)for c in columns]+[target.get(row,0)]for row in rows],P)
    rank_aug=aug.rank()
    label='constrained_' if constrained else ''
    report={'prime':P,'numerator_total_degree':degree,'feature':'k^2*(9eta+14)^2*P(eta,V)/(V*(eta+1)^2)' if constrained else 'P/[V*k*(9eta+14)*(eta*V^2-1)*(eta+1)^4]','rows':len(rows),'columns':len(columns),'rank':rank,'augmented_rank':rank_aug,'consistent':rank==rank_aug,'seconds':round(time.monotonic()-start,3),'scope':'Finite GF(p) leading-source ansatz on generic s=0 only; not a global scalar or certificate conclusion.'}
    (HERE/f'leading_{label}d{degree}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)
    if rank==rank_aug:
        import pickle
        (HERE/f'leading_{label}d{degree}.pickle').write_bytes(pickle.dumps({'monomials':mons,'rows':rows,'columns':columns,'target':target}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=20);ap.add_argument('--constrained',action='store_true');args=ap.parse_args();run(args.degree,args.constrained)
