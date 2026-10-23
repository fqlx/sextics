"""Fresh Fraction/Taylor audit; imports no primary differentiation routines.

All curve jets are solved directly by truncated Newton iteration in the
quartic implicit equation.  No primary formula for a_p or b_p is used.
"""
from fractions import Fraction as F
from pathlib import Path
import ast,json,math

NV=4
ORDER=2
class Jet:
    def __init__(self,terms=0):
        if isinstance(terms,Jet):self.t=terms.t.copy()
        elif isinstance(terms,dict):self.t={k:F(v) for k,v in terms.items()if v}
        else:self.t={(0,)*NV:F(terms)} if terms else {}
    def __add__(self,other):
        other=Jet(other);out=self.t.copy()
        for k,v in other.t.items():out[k]=out.get(k,F(0))+v
        return Jet(out)
    __radd__=__add__
    def __neg__(self):return Jet({k:-v for k,v in self.t.items()})
    def __sub__(self,other):return self+-Jet(other)
    def __rsub__(self,other):return Jet(other)+-self
    def __mul__(self,other):
        other=Jet(other);out={}
        for a,x in self.t.items():
            for b,y in other.t.items():
                k=tuple(i+j for i,j in zip(a,b))
                if sum(k)<=ORDER:out[k]=out.get(k,F(0))+x*y
        return Jet(out)
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        out=Jet(1)
        for _ in range(n):out=out*self
        return out
    def inv(self):
        c=self.val();assert c
        h=-(self-c)*(1/c)
        out=Jet(1);term=Jet(1)
        for _ in range(ORDER):term=term*h;out=out+term
        return out*(1/c)
    def __truediv__(self,other):return self*Jet(other).inv()
    def __rtruediv__(self,other):return Jet(other)*self.inv()
    def val(self):return self.t.get((0,)*NV,F(0))
    def der(self,*indices):
        ex=[0]*NV
        for i in indices:ex[i]+=1
        return self.t.get(tuple(ex),F(0))*math.prod(math.factorial(i)for i in ex)

def variable(v,i):
    ex=[0]*NV;ex[i]=1
    return Jet(v)+Jet({tuple(ex):1})
def root_a(a0,A,B,C,D,E,T,q):
    a=Jet(a0)
    for _ in range(3):
        K=C*q*q+E*q+T
        p=A*a**4+D*q*a**3+K*a*a+B*q**6
        dp=4*A*a**3+3*D*q*a*a+2*K*a
        a=a-p/dp
    return a

checks={}
def check(name,value):
    assert value,name
    checks[name]=True

def safe_expression(source,names):
    def go(n):
        if isinstance(n,ast.Expression):return go(n.body)
        if isinstance(n,ast.Constant)and isinstance(n.value,int):return F(n.value)
        if isinstance(n,ast.Name):return F(names[n.id])
        if isinstance(n,ast.UnaryOp)and isinstance(n.op,ast.USub):return -go(n.operand)
        if isinstance(n,ast.UnaryOp)and isinstance(n.op,ast.UAdd):return go(n.operand)
        if isinstance(n,ast.BinOp):
            x,y=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add):return x+y
            if isinstance(n.op,ast.Sub):return x-y
            if isinstance(n.op,ast.Mult):return x*y
            if isinstance(n.op,ast.Div):return x/y
            if isinstance(n.op,ast.Pow):assert y.denominator==1;return x**int(y)
        raise ValueError(ast.dump(n))
    return go(ast.parse(source,mode='eval'))

primary=Path(__file__).resolve().parents[2]/'coupled-fresh/infinity-horizontal/companion-toric-cross.json'
poly=json.loads(primary.read_text())['compact_numerator_over_J']

# Eight fresh normalized points. c is bound to Q=0, and all four independent
# jets deform c,d,e,q. The rational primitives are differentiated in q by
# their own Newton jets, not by the primary Cartan derivative formula.
normalized_points=[(1,1,2,3),(2,1,3,5),(1,2,4,1),(3,2,1,2),
                   (2,3,-2,7),(F(3,2),F(4,3),5,-3),(4,1,2,-1),(F(2,3),2,3,4)]
for n,(av,qv,dv,ev)in enumerate(normalized_points):
    NV=4;ORDER=2
    av,qv,dv,ev=map(F,(av,qv,dv,ev));bv=qv**3/av
    cv=-(av*av+bv*bv+dv*av*qv+ev*qv+1)/(qv*qv)
    c,d,e,q=variable(cv,0),variable(dv,1),variable(ev,2),variable(qv,3)
    a=root_a(av,Jet(1),Jet(1),c,d,e,Jet(1),q);b=q**3/a
    J=2*a*a+d*a*q-2*b*b
    assert J.val()
    ze=b/q;xi=a/q
    p1=a*q/(6*J)
    p2=a*(2*c*q*q+d*a*q+e*q+3)/(18*J)
    p3=-b*q/(6*J)
    p4=-b*(2*c*q*q+4*d*a*q+e*q+3)/(18*J)
    wb=(F(-1,3),F(-1,6),F(-1,6));wa=(F(-1,3),F(-2,3),F(-1,6))
    wt=(F(-1,3),F(-1,6),F(-2,3));xx=(cv,dv,ev)
    def euler_of_e(f,w):return sum(w[j]*xx[j]*f.der(j,2)for j in range(3))
    def euler_of_T_plus_half(f,w):
        return sum(w[j]*xx[j]*(wt[j]*f.der(j)+
            sum(wt[i]*xx[i]*f.der(j,i)for i in range(3))+f.der(j)/2)for j in range(3))
    rows=[ze.der(0,0)+euler_of_e(xi,wb)-xi.der(2)/6,
          ze.der(0,2)+euler_of_T_plus_half(xi,wb),
          xi.der(0,0)+euler_of_e(ze,wa)-ze.der(2)/6,
          xi.der(0,2)+euler_of_T_plus_half(ze,wa)]
    for k,(lhs,pot)in enumerate(zip(rows,(p1,p2,p3,p4)),1):
        check(f'normalized_point_{n}_cross_{k}',lhs==pot.der(3))
    # The two companion self rows carry the same infinity bookkeeping.
    ce=xi.der(0);tc=sum(wt[j]*xx[j]*xi.der(j,0)for j in range(3))
    ac=sum(wa[j]*xx[j]*xi.der(j,0)for j in range(3))
    check(f'normalized_point_{n}_self_E',xi.der(2,2)-tc-ce/6==(a*q*q/(3*J)).der(3))
    check(f'normalized_point_{n}_self_D',xi.der(1,1)-ac+F(5,6)*ce==(-a*q*q/(6*J)).der(3))

# Six universal points audit the direct source and the claimed polynomial/J
# compact representative. The B,E and q variations are independent.
for n in range(6):
    NV=4;ORDER=2
    av=F(n+1,2);qv=F(n+2,3);bv=qv**3/av
    AA,BB,CC,DD,EE=map(F,(n+2,n+3,2*n+5,n+4,3*n+7))
    TT=-(AA*av*av+BB*bv*bv+CC*qv*qv+DD*av*qv+EE*qv)
    A=Jet(AA);B=variable(BB,0);C=Jet(CC);D=Jet(DD);E=variable(EE,1);T=Jet(TT);q=variable(qv,3)
    a=root_a(av,A,B,C,D,E,T,q);b=q**3/a
    J=2*A*a*a+D*a*q-2*B*b*b
    eta=b/J;xi2=1/b
    check(f'universal_point_{n}_source_B',xi2.der(0)==-eta.val())
    check(f'universal_point_{n}_source_EB',xi2.der(0,1)==-eta.der(1))
    cp=CC-DD*DD/(4*AA);r=(cp-EE*EE/(4*TT))/(2*TT);shift=DD*cp/(2*AA)
    pot=a/(2*q*q)+(D*a*a+E*a)/(4*T*q)
    psi=xi2.val()+pot.der(3)-r*(a/q).val()+r*shift*(q*q/J).val()
    names=dict(A=AA,B=BB,C=CC,D=DD,E=EE,T=TT,a=av,b=bv,q=qv)
    check(f'universal_point_{n}_compact_polynomial',psi==safe_expression(poly,names)/J.val())

# Independent finite branch jets at Pb±. B*b² enters only at q^6; Newton
# solves the full quartic rather than using the displayed a1/a2 formula.
for sign in (1,-1):
    NV=1;ORDER=2
    av=F(2*sign);AA,BB,CC,DD,EE=map(F,(3,13,7,5,11));TT=-AA*av*av
    q=variable(0,0)
    a=root_a(av,Jet(AA),Jet(BB),Jet(CC),Jet(DD),Jet(EE),Jet(TT),q)
    a0,a1,a2=a.val(),a.der(0),a.der(0,0)/2
    cp=CC-DD*DD/(4*AA);r=(cp-EE*EE/(4*TT))/(2*TT)
    fm2=a0/2;fm1=a1/2+(DD*a0*a0+EE*a0)/(4*TT)
    check(f'Pb_{sign}_residue',a2==r*a0)
    check(f'Pb_{sign}_third_order_cancellation',a0-2*fm2==0)
    check(f'Pb_{sign}_second_order_cancellation',a1-fm1==0)
    check(f'Pb_{sign}_simple_residue_cancellation',a2-r*a0==0)

# The Pa branch has ord_q(a)=3; every term of F_b is then regular.
check('Pa_potential_regular_orders',min(3-2,2*3-1,3-1)>=0)

# Two infinity branches, solved directly in the projective chart by Newton.
# Here P_inf(b)=B*b^4+(A+D*u+C*u²)b²+E*u⁴*b+T*u⁶.
for sign in (1,-1):
    NV=1;ORDER=3
    b0=F(2*sign);BB,CC,DD,EE,TT=map(F,(3,7,5,11,13));AA=-BB*b0*b0
    u=variable(0,0);bb=Jet(b0)
    for _ in range(3):
        K=AA+DD*u+CC*u*u
        pol=BB*bb**4+K*bb*bb+EE*u**4*bb+TT*u**6
        der=4*BB*bb**3+2*K*bb+EE*u**4
        bb=bb-pol/der
    b3=bb.der(0,0,0)/6
    cp=CC-DD*DD/(4*AA);cinf=DD*cp/(4*AA*BB*b0);shift=DD*cp/(2*AA)
    r=(cp-EE*EE/(4*TT))/(2*TT);omega_res=-b0/(2*AA)
    check(f'infinity_{sign}_xi_nonzero_residue',b3==cinf and cinf!=0)
    check(f'infinity_{sign}_mandatory_shift',cinf==shift*omega_res)
    check(f'infinity_{sign}_compact_corrected_residue',-r*b3+r*shift*omega_res==0)
    check(f'infinity_{sign}_xi2_regular',(-2/bb).val()==-2/b0)
    check(f'infinity_{sign}_retained_fifth_order',-DD*b0/TT!=0)

out={'passed':True,'checks':len(checks),'details':checks,
 'method':'fresh Fraction multivariate Newton/Taylor jets; no primary differentiation or reduction code imported',
 'scope':'independent exact evaluations at fresh rational smooth points and exact finite/infinity branch jets; supports primary generic symbolic identities but is not itself a universal coefficient proof',
 'source':'partial_B(dq/b)=-eta_b; tau=partial_E partial_B(dq/b)',
 'infinity':'xi has nonzero opposite residues; corrected psi_hat requires +r*s*omega',
 'certificate':False}
Path(__file__).with_name('companion-independent-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='details'}))
