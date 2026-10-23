"""Direct global FLINT exterior derivative of ONE explicit original-field current.
No sequential main-term compression; no coefficient search.  Prefix still open.
"""
from pathlib import Path
import json,time
import flint
CTX=flint.fmpq_mpoly_ctx.get(['x','y','z','p'])
class RF:
 def __init__(self,n=0,d=1):
  if isinstance(n,RF):self.n,self.d=n.n,n.d;return
  self.n=n if isinstance(n,flint.fmpq_mpoly)else CTX.constant(n)
  self.d=d if isinstance(d,flint.fmpq_mpoly)else CTX.constant(d)
  if not self.d:raise ZeroDivisionError
  if not self.n:self.d=CTX.constant(1);return
  g=self.n.gcd(self.d);self.n=self.n//g;self.d=self.d//g
 def __add__(self,o):
  o=RF(o);g=self.d.gcd(o.d);ad=self.d//g;bd=o.d//g
  return RF(self.n*bd+o.n*ad,ad*o.d)
 __radd__=__add__
 def __neg__(self):return RF(-self.n,self.d)
 def __sub__(self,o):return self+-RF(o)
 def __rsub__(self,o):return RF(o)+-self
 def __mul__(self,o):
  o=RF(o);g=self.n.gcd(o.d);h=o.n.gcd(self.d)
  return RF((self.n//g)*(o.n//h),(self.d//h)*(o.d//g))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=RF(o)
  if not o.n:raise ZeroDivisionError
  return self*RF(o.d,o.n)
 def __rtruediv__(self,o):return RF(o)/self
 def __pow__(self,k):return RF(self.n**k,self.d**k)if k>=0 else RF(self.d**(-k),self.n**(-k))
 def diff(self,i):return RF(self.n.derivative(i)*self.d-self.n*self.d.derivative(i),self.d*self.d)
 def __eq__(self,o):
  o=RF(o);return self.n*o.d==o.n*self.d
 def __bool__(self):return bool(self.n)
 def info(self):return {'numerator_terms':len(self.n),'denominator_terms':len(self.d),'numerator_degree':int(self.n.total_degree()),'denominator_degree':int(self.d.total_degree())}
 def at(self,p):return self.n(*p)/self.d(*p)

def d(f):return[f.diff(i)for i in range(3)]
def w2(a,b):return[a[0]*b[1]-a[1]*b[0],a[0]*b[2]-a[2]*b[0],a[1]*b[2]-a[2]*b[1]]
def wadd(a,b):return[x+y for x,y in zip(a,b)]
def sc(c,a):return[c*x for x in a]
def w21(a,b):return a[0]*b[2]-a[1]*b[1]+a[2]*b[0]
def d2(a):return a[2].diff(0)-a[1].diff(1)+a[0].diff(2)
def at_aq(poly,aval,qval,zval):
 # For the actual (a=x³,q=xy) chart, keep the common x-character explicitly.
 dd=poly.to_dict(); rr={(i-j)%3 for i,j,k in dd}
 assert len(rr)==1,rr
 ch=next(iter(rr));res=flint.fmpq(0)
 for (i,j,k),cc in dd.items():res+=cc*aval**((i-j-ch)//3)*qval**j*zval**k
 return ch,res
def at_original_aq(ff,aval,qval,zval):
 cn,vn=at_aq(ff.n,aval,qval,zval);cd,vd=at_aq(ff.d,aval,qval,zval)
 assert cn==cd,(cn,cd)
 return vn/vd

def build():
 x,y,z,p=map(RF,CTX.gens());q=x*y;t=q/z**2;U=x**3+y**3;W=x**3-y**3
 gp=2*q**3-z**6;lam=q*z/2;H=1+x**6+y**6+z**6+q*z/2;C=x**3*z/2+q/3;hh=H-1;Dp=lam**2-4*hh*gp;Jmix=z**6*H-2*q**3
 A=3*x**6+3*y**6-3-9*z**6-x*y*z;P=-12*x**6-12*y**6-6-72*z**6-x*y*z;B=U/W-1
 F0=P*z**8/(72*q*A**2*Jmix)
 Qclear=wadd(wadd(sc(2*gp*(2*gp-lam),d(U)),sc(2*gp*U,d(lam))),sc(-U*(2*gp+lam),d(gp)))
 K0psi=w2(sc(2/(Dp*z**3),wadd(sc(t*H*hh*z**6/gp,d(t)),sc(-t*t/3,d(H)))),Qclear)
 P_high=3*U*(U+W)/(16*gp);kap=4*q**3/gp
 Omega=wadd(sc(2,d(P_high)),sc(3*U/(16*W),d(kap)))
 rpcoef=gp*(3*Dp-2*lam*hh*(3*H+2*t**3+2))/(36*t*z**9*lam*Dp)
 r0psi=sc(rpcoef,Qclear)
 q2Y=sc(y**3/(6*A),[-z,-y,x]);q3Y=-y**3/(6*A)
 q2CM=sc(B*F0,K0psi);q2G=sc(RF(-16)/3*F0,w2(Omega,r0psi))
 return locals()

def whole_raw(data):
 q2=wadd(wadd(data['q2Y'],data['q2CM']),data['q2G']);q3=data['q3Y'];H=data['H'];C=data['C'];y=data['y']
 # J=q2*theta0+q3*dxdydz*p/Z.  The latter is differentiated LITERALLY.
 # d_p(p/Z)=-2theta0-3HthetaH-2CthetaC.
 return {'theta0':d2(q2)+2*q3,'thetaH':w21(q2,d(H))+3*H*q3-y**3/6,'thetaC':w21(q2,d(C))+2*C*q3}

def audit_form(data,q2,q3):
 # Most general hyperelliptic-odd rational current:
 # J=sum_ij q2_ij dx_i dx_j dp/Z + q3 dxdydz/Z.
 # Higher odd Z poles are absorbed as powers of f in the rational q's.
 H=data['H'];C=data['C'];p=data['p'];y=data['y'];L=H+C*p;ff=L*L-4*p**6
 return ff*(d2(q2)-q3.diff(3))-L*w21(q2,wadd(d(H),sc(p,d(C))))+q3*(C*L-12*p**5)+y**3*L/6

if __name__=='__main__':
 start=time.time();data=build();raw=whole_raw(data)
 q2=wadd(wadd(data['q2Y'],data['q2CM']),data['q2G']);q3=data['q3Y']*data['p']
 E=audit_form(data,q2,q3);H=data['H'];C=data['C'];p=data['p'];L=H+C*p;ff=L*L-4*p**6
 checks={'WHOLE_literal_endpoint_derivative_matches_all_raw_rows':E==ff*raw['theta0']-L*(raw['thetaH']+p*raw['thetaC'])}
 assert all(checks.values()),checks
 out={'status':'DIRECT_WHOLE_ORIGINAL_FIELD_HYPERELLIPTIC_CURRENT_AUDITOR_READY; THREE_CURRENT_PREFIX_OPEN','method':'Native FLINT fractions in Q(x,y,z,p), Z²=f=(H+Cp)²−4p⁶. Differentiates the complete actual rational current before compact reduction. All Z poles, endpoint rows and fiber cochains are retained.','general_current':'J=sum_ij q2_ij(x,y,z,p) dx_i wedge dx_j wedge dp/Z+q3(x,y,z,p)dx wedge dy wedge dz/Z. Any higher odd Z pole is included by absorbing powers of f into the rational q coefficients.','WHOLE_exact_zero_test':'E=f*(d_base q2−partial_p q3)−(H+Cp)*[q2 wedge(dH+p dC)] +q3*[C(H+Cp)−12p⁵]+y³(H+Cp)/6. Then dJ−beta_original=E*dxdy dz dp/Z³. A genuine candidate passes exactly when the numerator of E is the zero polynomial.','checks':checks,'prefix_E':E.info(),'prefix_is_closed':not bool(E),'API':'build() gives all actual original-field components; audit_form(data,q2,q3) returns the exact rational obstruction. Add the fourth source-bound current to q2,q3 and require not bool(E).','elapsed_seconds':round(time.time()-start,3)}
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
