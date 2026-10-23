"""Source-compatible global-Y quotient and exact first-IBP residual jets.

The output keeps the cubic-root character rho^3=M throughout. No scalar
projection, fixed invariant level, or source multiplier is discarded.
"""
from pathlib import Path
import json,pickle,time
import sympy as s
from flint import fmpq,fmpq_mat

HERE=Path(__file__).parent
start=time.monotonic()
a,b,v,h,W,t,T,rho=s.symbols('a b v h W t T rho')
base=(a,b,v)
c=s.Rational(5,7)
B=b*(1+a*v)
P=1+v**6
Q=c*a*b*v
R=c*(a*b+v*b**3)
S=1+a**6+b**6
oldC=W**6+c*(h**3+B*h*t)*W**3+P*h**6+Q*h**4*t+R*h*h*t*t+S*t**3

# Independent literal substitution into the original six-variable equation.
x0,x1,x2,y0,y1,y2,y=s.symbols('X0 X1 X2 Y0 Y1 Y2 y')
physical=(x0**6+x1**6+x2**6+y0**6+y1**6+y2**6
          +c*(x0**3*x1*y0*y1+x0**3*x2**3+x0*x2**3*y1*y2
               +x1*x2**3*y0*y1+x0*x1*y1**3*y2+x0*x0*y0*y1*y2*y2))
sub={x0:h,x1:v*h,x2:W,y0:a*y,y1:b*y,y2:y}
assert s.expand(physical.subs(sub)-oldC.subs(t,y*y))==0
affine_map=s.Matrix([v,W,a*y,b*y,y])
affine_jac=s.det(affine_map.jacobian([v,W,a,b,y]))
assert affine_jac==y*y
# A=a^3*y^3 on h=1, so A*Jac*dy=(a^3/2)*t^2 dt.
assert s.cancel(a**3*y**3*affine_jac/(2*y)-a**3*(y*y)**2/2)==0

beta=-R/(3*S)
M=1+B*beta
alpha=M/B
LL=(P+Q*beta+R*beta*beta+S*beta**3)/(M*M)
rr=(Q-R*R/(3*S))/(B*M)
xx=B**3/(S*M)
canonical=W**6+c*(h**3+h*T)*W**3+LL*h**6+rr*h**4*T+T**3/xx
# Verify the shift/scale over the independent coefficient field first;
# expanding its physical rational pullback is unnecessarily expensive.
BB,PP,QQ,RR,SS=s.symbols('B0 P0 Q0 R0 S0')
be=-RR/(3*SS);mm=1+BB*be;al=mm/BB
ll=(PP+QQ*be+RR*be**2+SS*be**3)/mm**2
rr0=(QQ-RR**2/(3*SS))/(BB*mm);xx0=BB**3/(SS*mm)
formal=W**6+c*(h**3+BB*h*t)*W**3+PP*h**6+QQ*h**4*t+RR*h*h*t*t+SS*t**3
formal_new=W**6+c*(h**3+h*T)*W**3+ll*h**6+rr0*h**4*T+T**3/xx0
transformed=s.Poly(formal,W)
changed=0
for (power,),co in transformed.terms():
    assert power%3==0
    changed+=co.subs(t,al*T+be*h*h)*mm**(power//3)*W**power
assert s.cancel(changed-mm*mm*formal_new)==0

g0=a**3/(2*B*M**3)
assert s.cancel(alpha/(2*M**4)*a**3-g0)==0
fT=a**3/(2*B**3*M)
f0r=a**3*beta/(B*B*M*M)
f0L=a**3*beta*beta/(2*B*M**3)
assert all(s.cancel(x-y)==0 for x,y in [(fT,g0*alpha**2),(f0r,2*g0*alpha*beta),(f0L,g0*beta**2)])
coordinates=(LL,rr,xx)
J=s.Matrix([[s.diff(f,z)for z in base]for f in coordinates])

# Ten-coefficient second Taylor jets: exact numeric differentiation without
# expanding the large physical rational pullback.
exps=[(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(1,1,0),(1,0,1),(0,2,0),(0,1,1),(0,0,2)]
index={e:i for i,e in enumerate(exps)}
products=[(i,j,index[tuple(x+y for x,y in zip(e,f))])for i,e in enumerate(exps)for j,f in enumerate(exps)if sum(e)+sum(f)<=2]
class Jet:
    def __init__(self,value=0):self.c=[fmpq(value)]+[fmpq(0)]*(len(exps)-1)
    @staticmethod
    def coerce(x):return x if isinstance(x,Jet)else Jet(x)
    def __add__(self,x):
        x=self.coerce(x);z=Jet();z.c=[a+b for a,b in zip(self.c,x.c)];return z
    __radd__=__add__
    def __neg__(self):
        z=Jet();z.c=[-a for a in self.c];return z
    def __sub__(self,x):return self+-self.coerce(x)
    def __rsub__(self,x):return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x);z=Jet()
        for i,j,k in products:z.c[k]+=self.c[i]*x.c[j]
        return z
    __rmul__=__mul__
    def inv(self):
        assert self.c[0];eps=Jet();eps.c=self.c.copy();eps.c[0]=0
        a=self.c[0]
        return Jet(1/a)-eps*(1/(a*a))+eps*eps*(1/(a*a*a))
    def __truediv__(self,x):return self*self.coerce(x).inv()
    def __rtruediv__(self,x):return self.coerce(x)*self.inv()
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        z=Jet(1);x=self
        while n:
            if n&1:z=z*x
            n//=2
            if n:x=x*x
        return z
    def grad(self):return self.c[1:4]
    def hessian(self):
        return [[self.c[index[tuple(int(k==i)+int(k==j)for k in range(3))]]*(2 if i==j else 1)for j in range(3)]for i in range(3)]

def exact_point(point):
    aa,bb,vv=[Jet(p)for p in point]
    for i,z in enumerate([aa,bb,vv]):z.c[i+1]=1
    bc=bb*(1+aa*vv);pc=1+vv**6;qc=fmpq(5,7)*aa*bb*vv
    rc=fmpq(5,7)*(aa*bb+vv*bb**3);sc=1+aa**6+bb**6
    betac=-rc/(3*sc);mc=1+bc*betac
    lc=(pc+qc*betac+rc*betac**2+sc*betac**3)/(mc**2)
    rrc=(qc-rc**2/(3*sc))/(bc*mc);xc=bc**3/(sc*mc)
    ffT=aa**3/(2*bc**3*mc);ff0r=aa**3*betac/(bc**2*mc**2);ff0L=aa**3*betac**2/(2*bc*mc**3)
    jets=[lc,rrc,xc]
    jm=fmpq_mat([f.grad()for f in jets])
    det=jm.det()
    assert det!=0
    ji=jm.inv()
    dlogJ=[]
    for z in range(3):
        dj=fmpq_mat([[f.hessian()[i][z]for i in range(3)]for f in jets])
        prod=ji*dj
        dlogJ.append(sum(prod[i,i]for i in range(3)))
    mval=mc.c[0]
    qvec=[z/(3*mval)for z in mc.grad()]
    VL=[ji[i,0]for i in range(3)];Vr=[ji[i,1]for i in range(3)]
    def charged_div(f,vec):
        fv=f.c[0];df=f.grad()
        return sum(vec[i]*(df[i]+fv*(qvec[i]-dlogJ[i]))for i in range(3))
    RT=charged_div(ffT,Vr)
    Rzero=charged_div(ff0r,Vr)+charged_div(ff0L,VL)
    return {'point':list(map(str,point)),'M':str(mval),'jacobian':str(det),
            'canonical_parameters':[str(f.c[0])for f in jets],
            'R_T_divided_by_rho':str(RT),'R_0_divided_by_rho':str(Rzero),
            'R_T_zero':RT==0,'R_0_zero':Rzero==0}

points=[exact_point(p)for p in [(1,2,3),(2,1,3),(2,3,1)]]
packet={'symbols':{'a':a,'b':b,'v':v,'h':h,'W':W,'t':t,'T':T},
        'c':c,'B':B,'P':P,'Q':Q,'R':R,'S':S,'beta':beta,'M':M,'alpha':alpha,
        'L':LL,'r':rr,'x':xx,'source_prefactor_without_rho':g0,
        'source_polynomial':(alpha*T+beta*h*h)**2*h**4,
        'first_current_coefficients':{'T_r':fT,'zero_r':f0r,'zero_L':f0L},'jacobian_matrix':J}
(HERE/'source_model.pickle').write_bytes(pickle.dumps(packet))
report={
 'target':'cyclic-triple-residual; exact original sextic, c=5/7, A=X0^3 Y0^3',
 'physical_coordinates':'X0=h,X1=v*h,X2=W,Y0=a*y,Y1=b*y,Y2=y,t=y^2',
 'curve':str(oldC),
 'physical_source':'(a^3/2)*h^4*t^2*Omega_(h,W,t)/C^2 wedge da db dv; Omega|h1=dW wedge dt',
 'canonical_transform':'t_old=alpha*T+beta*h^2,W_old=rho*W,rho^3=M; C_old=M^2*C_new',
 'parameters':{name:str(value)for name,value in [('B',B),('beta',beta),('M',M),('alpha',alpha),('L',LL),('r',rr),('x',xx)]},
 'canonical_source':'rho*g0*[alpha^2*eta(T^2)+2alpha*beta*eta(T)+beta^2*eta(1)]',
 'g0':str(g0),
 'eta_derivatives':'eta(T^2)=-nabla_r(omega1),eta(T)=-nabla_r(omega0),eta(1)=-nabla_L(omega0); omega0=h^2 Omega/C,omega1=T Omega/C',
 'first_current':'J0=-i_(rho*fT*V_r)(da db dv) wedge omega1-i_(rho*(f0r*V_r+f0L*V_L))(da db dv) wedge omega0, with required fiber-exact connection corrections',
 'remainder':'source=dJ0+rho*(R_T*omega1+R_0*omega0) wedge da db dv modulo the retained fiber-exact corrections',
 'R_T':'V_r(fT)+fT*(V_r(log M)/3-V_r(log Jac))',
 'R_0':'V_r(f0r)+f0r*(V_r(log M)/3-V_r(log Jac))+V_L(f0L)+f0L*(V_L(log M)/3-V_L(log Jac))',
 'Piola':'div(Jac*V_i)=0; V_i=(d(L,r,x)/d(a,b,v))^-1 column_i',
 'first_current_coefficients':{name:str(value)for name,value in [('fT',fT),('f0r',f0r),('f0L',f0L)]},
 'exact_jet_points':points,
 'scope':'Exact source transport and first integration by parts. Nonzero residuals remain; no primitive or certificate asserted.',
 'seconds':round(time.monotonic()-start,3),
}
(HERE/'source_model.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
