"""Independent second Taylor jets and physical marked-log chart operators."""
from pathlib import Path
import itertools,pickle,json,time,argparse,random
from fractions import Fraction
from flint import fmpq_mpoly_ctx,fmpq_mpoly,nmod_mat
ROOT=Path(__file__).parent
EXPS=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(1,1,0),(1,0,1),(0,2,0),(0,1,1),(0,0,2)]
IDX={e:i for i,e in enumerate(EXPS)}
PRODUCT=[(i,j,IDX[tuple(a+b for a,b in zip(e,f))])for i,e in enumerate(EXPS)for j,f in enumerate(EXPS)if sum(e)+sum(f)<=2]
def qmod(c,p):
    v=Fraction(str(c));return v.numerator*pow(v.denominator,-1,p)%p
class J1:
    p=1000003
    def __init__(self,v=0,g=None):self.v=int(v)%self.p;self.g=tuple(int(z)%self.p for z in (g or (0,0,0)))
    def __add__(a,b):
        b=b if isinstance(b,J1)else J1(b);return J1(a.v+b.v,[x+y for x,y in zip(a.g,b.g)])
    __radd__=__add__
    def __neg__(a):return J1(-a.v,[-v for v in a.g])
    def __sub__(a,b):return a+-b
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        b=b if isinstance(b,J1)else J1(b);return J1(a.v*b.v,[a.v*y+x*b.v for x,y in zip(a.g,b.g)])
    __rmul__=__mul__
    def __pow__(a,n):
        v=pow(a.v,n,a.p);co=(n*pow(a.v,n-1,a.p))%a.p if n else 0
        return J1(v,[co*x for x in a.g])
    def __truediv__(a,b):return a*(b if isinstance(b,J1)else J1(b))**-1
    def __rtruediv__(a,b):return b*a**-1
class J2:
    p=1000003
    def __init__(self,v=0,seed=None,coeff=None):
        self.c=[int(z)%self.p for z in coeff]if coeff is not None else [int(v)%self.p]+[0]*9
        if seed is not None:self.c[seed+1]=1
    def __add__(a,b):
        b=b if isinstance(b,J2)else J2(b);return J2(coeff=[x+y for x,y in zip(a.c,b.c)])
    __radd__=__add__
    def __neg__(a):return J2(coeff=[-z for z in a.c])
    def __sub__(a,b):return a+-b
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        b=b if isinstance(b,J2)else J2(b);out=[0]*10
        for i,j,k in PRODUCT:out[k]+=a.c[i]*b.c[j]
        return J2(coeff=out)
    __rmul__=__mul__
    def inv(a):
        ai=pow(a.c[0],-1,a.p);delta=J2(coeff=[0]+a.c[1:]);return J2(ai)-delta*(ai*ai)+delta*delta*(ai**3)
    def __pow__(a,n):
        if n<0:return a.inv()**(-n)
        out=J2(1)
        while n:
            if n&1:out*=a
            n//=2
            if n:a*=a
        return out
    def __truediv__(a,b):return a*(b if isinstance(b,J2)else J2(b)).inv()
    def __rtruediv__(a,b):return b*a.inv()
    def first(a):return J1(a.c[0],a.c[1:4])
    def derivative(a,i):
        return J1(a.c[i+1],[a.c[IDX[tuple(int(k==i)+int(k==j)for k in range(3))]]*(2 if i==j else 1)for j in range(3)])
class Poly:
    def __init__(self,terms,p):self.p=p;self.terms=[(tuple(e),qmod(c,p))for e,c in terms.items()]
    def eval(self,args):
        cls=type(args[0]);out=cls(0);powers=[]
        for i,z in enumerate(args):
            pp=[cls(1)]
            for _ in range(max((e[i]for e,c in self.terms),default=0)):pp.append(pp[-1]*z)
            powers.append(pp)
        for e,c in self.terms:
            term=cls(c)
            for i,k in enumerate(e):term*=powers[i][k]
            out+=term
        return out
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),a[0]*0)
class PhysicalModel:
    def __init__(self,p=1000003):
        self.p=p;J1.p=J2.p=p;ctx=fmpq_mpoly_ctx.get(('L','r','x','s'));self.raw=pickle.loads((ROOT/'verified.pickle').read_bytes())
        def rat(e):return (Poly(fmpq_mpoly(e['numerator'],ctx).to_dict(),p),Poly(fmpq_mpoly(e['denominator'],ctx).to_dict(),p))
        self.W=[[(rat(e))for e in row]for row in self.raw['fields']]
        self.C=[[[rat(e)for e in row]for row in M]for M in self.raw['connection_contractions']]
        effective=pickle.loads(Path('/workspace/research/round9/cyclic_full/schiffer_audit.pickle').read_bytes());L,r,x,z=effective['symbols']
        import sympy as s
        n0,d0=s.fraction(effective['eta0']);n1,d1=s.fraction(effective['eta1']);ratio=s.cancel(n1*d0/(d1*n0));nn,dd=s.fraction(ratio)
        self.Te=(Poly(s.Poly(nn,L,r,x,z).as_dict(),p),Poly(s.Poly(dd,L,r,x,z).as_dict(),p))
        connection=pickle.loads(Path('/workspace/research/round10/horizontal5/rank5_connection.pickle').read_bytes())
        self.N={name:[[rat(e)for e in row]for row in M]for name,M in connection['connection'].items()}
    @staticmethod
    def evaluate(pair,args):return pair[0].eval(args)/pair[1].eval(args)
    def point(self,pt,pivot=0,normalized=True):
        p=self.p;J1.p=J2.p=p;a,b,v=[J2(pt[i],seed=i)for i in range(3)];c=qmod('5/7',p)
        E=1+a*v;B=b*E;P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6;A=3*S-B*R
        L=(27*P*S*S-9*Q*R*S+2*R**3)/(3*A*A);rr=(3*S*Q-R*R)/(B*A);x=3*B**3/A;z=B*R/A
        pars=[L,rr,x];mark=self.evaluate(self.Te,pars+[z]);args=[f.first()for f in pars+[mark]]
        jac=[[f.derivative(i)for i in range(3)]for f in pars];cof=[cross(jac[1],jac[2]),cross(jac[2],jac[0]),cross(jac[0],jac[1])];det=dot(jac[0],cof[0]);V=[[v/det for v in row]for row in cof]
        for i in range(3):
            for j in range(3):
                value=dot(jac[i],V[j]);assert value.v==int(i==j) and not any(value.g)
        W=[[self.evaluate(e,args)for e in row]for row in self.W];Xm=[[sum((W[k][j]*V[j][i]for j in range(3)),J1())for i in range(3)]for k in range(4)]
        md=[mark.derivative(i)for i in range(3)];psi=[W[k][3]-dot(Xm[k],md)for k in range(4)]
        conjet=[[[self.evaluate(e,args)for e in row]for row in mat]for mat in self.C]
        con=[[[e.v for e in row]for row in mat]for mat in conjet]
        logF=[(3*a.derivative(i).v*pow(a.c[0],-1,p)+qmod('2/3',p)*S.derivative(i).v*pow(S.c[0],-1,p)-3*b.derivative(i).v*pow(b.c[0],-1,p)-3*E.derivative(i).v*pow(E.c[0],-1,p)-qmod('2/3',p)*A.derivative(i).v*pow(A.c[0],-1,p))%p for i in range(3)]
        fT=(3*a**3*S/(2*B**3*A)).first();pairs={}
        for i in range(4):
            for j in range(i+1,4):
                F=[psi[j]*Xm[i][k]-psi[i]*Xm[j][k]for k in range(3)]
                N=[[(psi[j].v*con[i][a][b]-psi[i].v*con[j][a][b])%p for b in range(5)]for a in range(5)]
                pairs[(i,j)]=(F,N)
        charts=[]
        for j in range(4):
            if j==pivot:continue
            scale=psi[j]/psi[pivot]if normalized else psi[j]
            F=[Xm[j][k]-scale*Xm[pivot][k]for k in range(3)]if normalized else [psi[pivot]*Xm[j][k]-scale*Xm[pivot][k]for k in range(3)]
            NJ=[[conjet[j][a][b]-scale*conjet[pivot][a][b]for b in range(5)]for a in range(5)]if normalized else [[psi[pivot]*conjet[j][a][b]-scale*conjet[pivot][a][b]for b in range(5)]for a in range(5)]
            N=[[e.v for e in row]for row in NJ]
            div=sum(F[i].g[i]for i in range(3))%p;scalar=(div+sum(F[i].v*logF[i]for i in range(3)))%p
            charts.append(dict(index=j,field=F,matrix=N,matrix_jet=NJ,divergence=div,scalar=scalar))
        NL=[[self.evaluate(e,args)for e in row]for row in self.N['L']];Nr=[[self.evaluate(e,args)for e in row]for row in self.N['r']]
        z1=z.first();rhsjet=[-Nr[1][i]+2*z1*Nr[0][i]-z1*z1*NL[0][i]for i in range(5)];rhs=[v.v for v in rhsjet]
        return dict(pt=pt,pars=[f.c[0]for f in pars],mark=mark,z=z,psi=psi,pairs=pairs,charts=charts,logF=logF,fT=fT,rhs=rhs,rhs_jet=rhsjet,pivot=pivot)
def columns(d,p,densities=('rhofT','rho')):
    rows=[[]for _ in range(5)]
    for density in densities:
        f=J1(1)if density=='rhofT'else 1/d['fT']
        for ch in d['charts']:
            sc=(sum(ch['field'][i].v*f.g[i]for i in range(3))+ch['scalar']*f.v)%p
            for comp in range(5):
                for i in range(5):rows[i].append((f.v*ch['matrix'][comp][i]+(sc if i==comp else 0))%p)
    return rows

def hodge_leading(d,p,components=(0,1,3,4),higgs_pivot=(0,4),densities=('rhofT','rho')):
    """Algebraically match eta, leaving a four-row rational differential system.

    Each null direction stores both its zeroth-order image and its full
    physical principal symbol, so any coefficient function can be applied.
    """
    dirs=[(j,c)for j in range(3)for c in components];jp,cp=higgs_pivot
    assert (jp,cp)in dirs
    chp=d['charts'][jp];hp=chp['matrix_jet'][cp][2];f=d['rhs_jet'][2]/hp
    def image(ch,comp,coef):
        sc=(sum(ch['field'][i].v*coef.g[i]for i in range(3))+ch['scalar']*coef.v)%p
        return [(coef.v*ch['matrix'][comp][i]+(sc if i==comp else 0))%p for i in range(5)]
    particular=image(chp,cp,f);residual=[(a-b)%p for a,b in zip(d['rhs'],particular)];assert residual[2]==0
    target_rows=(0,1,3,4);operators=[];cols=[[]for _ in range(4)]
    for j,c in dirs:
        if (j,c)==higgs_pivot:continue
        ch=d['charts'][j];ratio=ch['matrix_jet'][c][2]/hp
        im0=image(ch,c,J1(1));imp=image(chp,cp,ratio);im=[(a-b)%p for a,b in zip(im0,imp)];assert im[2]==0
        symbol=[[0]*3 for _ in range(5)]
        for k in range(3):
            symbol[c][k]=(symbol[c][k]+ch['field'][k].v)%p
            symbol[cp][k]=(symbol[cp][k]-ratio.v*chp['field'][k].v)%p
        assert not any(symbol[2]);operators.append(dict(direction=(j,c),ratio=ratio,zeroth_order=[im[i]for i in target_rows],principal_symbol=[symbol[i]for i in target_rows]))
    for density in densities:
        g=J1(1)if density=='rhofT'else 1/d['fT']
        for op in operators:
            for i in range(4):cols[i].append((g.v*op['zeroth_order'][i]+sum(a*b for a,b in zip(op['principal_symbol'][i],g.g)))%p)
    return dict(pivot=higgs_pivot,particular_coefficient=f,particular_image=particular,residual=[residual[i]for i in target_rows],operators=operators,columns=cols,target_rows=target_rows,higgs_pivot_value=hp)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--prime',type=int,default=1000003);ap.add_argument('--pivots',default='0,1,2,3');args=ap.parse_args();p=args.prime;model=PhysicalModel(p);rng=random.Random(1061);start=time.monotonic();out=[]
    for pivot in map(int,args.pivots.split(',')):
        rows=[];rhs=[];points=[]
        while len(points)<30:
            pt=[rng.randrange(1,p)for i in range(3)]
            try:d=model.point(pt,pivot);cols=columns(d,p)
            except (ValueError,ZeroDivisionError):continue
            rows.extend(cols);rhs.extend(d['rhs']);points.append(pt)
        rank=nmod_mat(rows,p).rank();aug=nmod_mat([row+[v]for row,v in zip(rows,rhs)],p).rank();closure=nmod_mat([row for k,row in enumerate(rows)if k%5>=3],p).rank()
        out.append(dict(pivot=pivot,columns=30,rows=len(rows),rank=rank,augmented_rank=aug,boundary_rank=closure,boundary_kernel_dimension=30-closure))
    ans=dict(prime=p,chart_current_tests=out,seconds=time.monotonic()-start,scope='Natural normalized-chart constant coefficient modules only; no unrestricted obstruction.')
    (ROOT/'physical_tests.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
