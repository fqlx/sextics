"""Constructive exact finite-field search for the toric-section heat current.

Candidate w=H*f is required to solve P* w=H_ee. This program searches for a
solution; a failed finite span has no nonexistence meaning. A hit is only a
candidate until reconstructed over Q and verified as a literal identity.
"""
from pathlib import Path
from fractions import Fraction
import ast,json,random

P=1009
ORDER=3
ZERO=(0,0,0)
def scalar(x):
    if isinstance(x,Fraction):return x.numerator*pow(x.denominator,-1,P)%P
    return int(x)%P
class Jet:
    def __init__(self,x=0):self.c=({e:scalar(v) for e,v in x.items() if scalar(v)} if isinstance(x,dict) else ({ZERO:scalar(x)} if scalar(x) else {}))
    @property
    def value(self):return self.c.get(ZERO,0)
    def __add__(self,b):
        b=jet(b);out=self.c.copy()
        for e,v in b.c.items():out[e]=(out.get(e,0)+v)%P
        return Jet(out)
    __radd__=__add__
    def __neg__(self):return Jet({e:-v for e,v in self.c.items()})
    def __sub__(self,b):return self+-jet(b)
    def __rsub__(self,b):return jet(b)+-self
    def __mul__(self,b):
        b=jet(b);out={}
        for e,v in self.c.items():
            for f,w in b.c.items():
                g=tuple(x+y for x,y in zip(e,f))
                if sum(g)<=ORDER:out[g]=(out.get(g,0)+v*w)%P
        return Jet(out)
    __rmul__=__mul__
    def inverse(self):
        a=pow(self.value,-1,P);n=(self*a)-1
        ans=Jet(1);term=Jet(1)
        for j in range(1,ORDER+1):term=term*(-n);ans+=term
        return ans*a
    def __truediv__(self,b):return self*jet(b).inverse()
    def __rtruediv__(self,b):return jet(b)*self.inverse()
    def __pow__(self,n):
        if n<0:return self.inverse()**(-n)
        ans=Jet(1);a=self
        while n:
            if n&1:ans=ans*a
            n//=2
            if n:a=a*a
        return ans
    def partial(self,i):
        out={}
        for e,v in self.c.items():
            if e[i]:f=list(e);f[i]-=1;out[tuple(f)]=v*e[i]
        return Jet(out)
def jet(x):return x if isinstance(x,Jet) else Jet(x)
def variable(v,i):
    e=[0,0,0];e[i]=1
    return Jet({ZERO:v,tuple(e):1})
def fpow_unit(x,a):
    assert x.value==1
    n=x-1;ans=Jet(1);term=Jet(1);coef=Fraction(1)
    for j in range(1,ORDER+1):
        term=term*n;coef*=Fraction(a-j+1,j);ans+=scalar(coef)*term
    return ans
def evaluate(source,env):
    def visit(n):
        if isinstance(n,ast.Constant):return Jet(n.value)
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp):return -visit(n.operand) if isinstance(n.op,ast.USub) else visit(n.operand)
        if isinstance(n.op,ast.Pow):
            b=visit(n.right);exponent=b.value
            if exponent>P//2:exponent-=P
            return visit(n.left)**exponent
        a,b=visit(n.left),visit(n.right)
        if isinstance(n.op,ast.Add):return a+b
        if isinstance(n.op,ast.Sub):return a-b
        if isinstance(n.op,ast.Mult):return a*b
        return a/b
    return visit(ast.parse(source,mode='eval').body)
def action(V,f):return sum((V[i]*f.partial(i) for i in range(3)),Jet())

HERE=Path(__file__).parent
data=json.loads((HERE/'physical-source-adjoints.json').read_text())

def prepare(r0,k0,z0):
    R0=r0*r0%P;S0=pow(k0,6,P)*pow(R0,-1,P)%P
    R,S,z=[variable(v,i) for i,v in enumerate((R0,S0,z0))]
    k=Jet(k0)*fpow_unit(R/R0,Fraction(1,6))*fpow_unit(S/S0,Fraction(1,6))
    A=1+R;B=1+S;T=1+z**6
    Delta=3*R*S*z**6-3*R*S-8*R*z**6+R-S*z**6+2*S
    if any(not x.value for x in (A,B,T,Delta)):raise ZeroDivisionError
    env=dict(R=R,S=S,z=z,k=k)
    Y=[evaluate(data['E_lift'][c],env) for c in ('R','S','z')]
    Z=[T*evaluate(data['T_lift'][c],env) for c in ('R','S','z')]
    # Relative C variation sC=1/C. Eliminate the same six lift equations.
    ca=2-1/R-3/S;cz=-6+4/R+2/S;t=6*z**6/T
    relC=3/k
    const=relC*(2*(1+1/R)-2*(1+1/S)-6)
    vz=-const/(ca*t+cz);alpha=t*vz
    v=Fraction(3,2)*(alpha-vz);u=-relC-vz-v/3
    X=[A*(alpha-2*u-2*v),B*(alpha+2*u-2*v),z*vz]
    H=fpow_unit(T/T.value,Fraction(4,3))*fpow_unit(A/A.value,Fraction(11,6))*fpow_unit(B/B.value,Fraction(5,6))*(z0*k0*Delta.value)/(z*k*Delta)
    eps=fpow_unit(T/T.value,Fraction(-2,3))*fpow_unit(A/A.value,Fraction(-1,6))*fpow_unit(B/B.value,Fraction(-1,6))
    eps_log_Y=action(Y,eps)/eps
    shear=[evaluate(data['shear_lift'][c],env) for c in ('R','S','z')]
    DD=[shear[i]-(z*k/(4*A))*X[i] for i in range(3)]
    VA=[-(k/9)*X[i]-(z*k/3)*DD[i]-(z/12)*Y[i] for i in range(3)]
    VB=[-(k/9)*X[i]-(z*k/12)*DD[i]-(z/12)*Y[i] for i in range(3)]
    gamma=fpow_unit(T/T.value,Fraction(-1,6))*fpow_unit(A/A.value,Fraction(-2,3))*fpow_unit(B/B.value,Fraction(-1,6))
    gamma_log_D=action(DD,gamma)/gamma
    def op(F):return (action(Y,action(Y,F))-eps_log_Y*action(Y,F)-action(X,action(Z,F)-Fraction(4,3)*F)/T).value
    def op2(F):return ((A/T)*(action(DD,action(DD,F))-gamma_log_D*action(DD,F)-action(X,action(VA,F)-Fraction(5,6)*F)/A)).value
    alpha=fpow_unit(T/T.value,Fraction(-1,3))*fpow_unit(A/A.value,Fraction(-1,3))*fpow_unit(B/B.value,Fraction(-1,3))
    ax=action(X,alpha)/alpha
    az=action(Z,alpha)/alpha
    aa=action(VA,alpha)/alpha
    ab=action(VB,alpha)/alpha
    def op3(F):
        left=action(X,F)-ax*F
        left=action(X,left)-2*ax*left
        left=action(X,left)-3*ax*left
        right=action(Z,F)-(Fraction(5,3)+az)*F
        right=action(VB,right)-(Fraction(1,6)+ab)*right
        right=action(VA,right)-(Fraction(7,6)+aa)*right
        return (A*B*left-right/T).value
    rhs=(action(Y,action(Y,H))-eps_log_Y*action(Y,H)).value
    return env|dict(A=A,B=B,T=T,Delta=Delta),H,op,rhs,op2,op3

def rref_solve(rows,n):
    a=[r[:] for r in rows];row=0;piv=[]
    for c in range(n):
        k=next((i for i in range(row,len(a)) if a[i][c]),None)
        if k is None:continue
        a[row],a[k]=a[k],a[row];ii=pow(a[row][c],-1,P);a[row]=[v*ii%P for v in a[row]]
        for i in range(len(a)):
            if i!=row and a[i][c]:
                v=a[i][c];a[i]=[(x-v*y)%P for x,y in zip(a[i],a[row])]
        piv.append(c);row+=1
    consistent=all(any(r[:n]) or not r[n] for r in a)
    sol=[0]*n
    if consistent:
        for i,c in enumerate(piv):sol[c]=a[i][n]
    return consistent,len(piv),sol

def basis(mode):
    if mode=='elementary':
        return ['1','R','S','k','z','A','B','T','Delta','1/A','1/B','1/T','z**2','k**2','z*k','Delta/A','Delta/B','Delta/T']
    if mode=='polynomial':
        return [f'R**{i}*S**{j}*k**{l}*z**{m}' for i in range(2) for j in range(2) for l in range(3) for m in range(4)]
    if mode=='delta':
        return [f'Delta**{d}*k**{l}*z**{m}*A**{i}*B**{j}*T**{t}' for d in range(2) for l in range(2) for m in range(3) for i,j,t in [(0,0,0),(1,0,0),(0,1,0),(0,0,1)]]
    if mode=='source_poles':
        return ['1','Delta','1/Delta','R','S','k','z','z**2','k**2','z*k','Delta/A','Delta/B','Delta/T','1/A','1/B','1/T','R/Delta','S/Delta','k/Delta','z/Delta','z**2/Delta','k**2/Delta','z*k/Delta','T/Delta']
    raise ValueError(mode)

def main(mode='elementary',joint=False,third=False):
    base_names=basis(mode);names=base_names*(3 if third else 2 if joint else 1)
    rows=[];rng=random.Random(5710);points=[]
    for index in range(len(names)+12):
        while True:
            pt=tuple(rng.randrange(1,P) for _ in range(3))
            try:env,H,op,rhs,op2,op3=prepare(*pt);break
            except (ValueError,ZeroDivisionError):pass
        row=[op(H*evaluate(name,env)) for name in base_names]
        if joint or third:row += [op2(H*evaluate(name,env)) for name in base_names]
        if third:row += [op3(H*evaluate(name,env)) for name in base_names]
        rows.append(row+[rhs]);points.append(pt)
    ok,rank,sol=rref_solve(rows,len(names))
    out={'status':'candidate' if ok else 'no candidate in this constructive span',
         'prime':P,'mode':mode,'joint_second_box':joint or third,'joint_third_box':third,'basis_count':len(names),'row_count':len(rows),'rank':rank,
         'basis':names,'candidate_coefficients_mod_p':sol if ok else None,
         'literal_equation':'[YE²−(YE log epsilon)YE−(1/T)XC o(T VT−4/3)](H f)=[YE²−(YE log epsilon)YE]H',
         'scope':'candidate search only; failed spans are not exclusion results; any hit requires rational reconstruction and literal verification'}
    (HERE/f'heat-multiplier-{mode}{"-three" if third else "-joint" if joint else ""}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('basis','literal_equation')},indent=2))
if __name__=='__main__':
    import sys
    main(sys.argv[1] if len(sys.argv)>1 else 'elementary','--joint' in sys.argv,'--three' in sys.argv)
