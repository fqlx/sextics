"""Independent literal x,y,z,p audit of the one source-forced CM current.

Ordinary physical derivatives only; no quotient derivative/reduction imported.
The scalar in the CM piece is forced by its entire C-normal packet.
"""
from pathlib import Path
import json, time
import sympy as s

started=time.time()
x,y,z,p=s.symbols('x y z p', nonzero=True)
xx=(x,y,z)
def grad(v): return s.Matrix([s.diff(v,t) for t in xx])
def rat(v): return s.factor(s.cancel(v))
checks={}
def check(name,v):
    vv=s.cancel(v)
    checks[name]=vv==0
    if not checks[name]: raise AssertionError((name, vv))
    print('PASS', name, round(time.time()-started,3),flush=True)

u=x**3;w=y**2/x;q=x*y
eta=2*x**3+y**6/x**3-3*z**2/4
J=1+z**6+x**6+y**6-3*z**2*x**3/4
C=z*x**3/2+x*y/3
H=1+z**6+x**6+y**6+z*x*y/2
d=1+z**6-J
check('H_transport',H-J-3*z*C/2)
check('physical_jacobian',s.det(s.Matrix([grad(u).T,grad(w).T,grad(z).T]))-6*x*y)

a=y**3/(3*eta**2)
b=z*y**3/(12*eta)+y**4/(36*x**2*eta)
Kprior=s.Matrix([y**3/(18*x**2*eta),y**4/(36*x**3*eta),0])
divprior=sum(s.diff(Kprior[i],xx[i]) for i in range(3))
check('prior_whole_hol_density',divprior+a)
check('prior_whole_C_normal',Kprior.dot(grad(C))-b)
check('prior_whole_H_normal',Kprior.dot(grad(H))-y**3/6-3*z*b/2)

Ohat=s.Matrix([-8*y**6+3*z**2*x**3,8*x*y**5,-2*z*x**4])
Omega=-(grad(u)/u-grad(d)/(2*d))/(3*q*eta)
Oscale=-1/(8*x**2*y*eta*d)
for i in range(3): check('actual_absolute_Omega_'+str(i),Omega[i]-Oscale*Ohat[i])
contact=grad(J)+s.Matrix([0,0,3*C/2])
raw=Ohat.cross(contact)
mass=rat(raw.dot(grad(C)))
KCM=s.Matrix([rat(-b*v/mass) for v in raw])
forced=rat(-b/(Oscale*mass))
check('CM_whole_C_normal',KCM.dot(grad(C))+b)
check('CM_whole_H_normal',KCM.dot(grad(H))+3*z*b/2)
check('CM_contact_constraint',KCM.dot(contact))
Ktotal=s.Matrix([rat(Kprior[i]+KCM[i]) for i in range(3)])
check('combined_whole_C_normal',Ktotal.dot(grad(C)))
check('combined_whole_H_normal',Ktotal.dot(grad(H))-y**3/6)

# Match the independent construction to the exported candidate, including its
# unique scalar; the wedge-coordinate transformation uses no imported code.
parent_path=(Path(__file__).parents[1]/'fresh-algebraic-construction/actual_source_forced_odd_CM_contact_current.json')
parent=json.loads(parent_path.read_text())
pu,pw,pq,pz=s.symbols('u w q z',nonzero=True)
def pull(txt):
    return s.sympify(txt,locals={'u':pu,'w':pw,'q':pq,'z':pz}).subs({pu:u,pw:w,pq:q,pz:z},simultaneous=True)
PK=list(map(pull,parent['current_vector']))
PKphys=s.Matrix([2*y*PK[0]/x,y**2*PK[0]/x**2+3*x**2*PK[1],6*x*y*PK[2]])
for i in range(3): check('exported_whole_current_'+str(i),KCM[i]-PKphys[i])
check('exported_forced_scalar',forced-pull(parent['forced_scalar']))

# Literal ordinary curvature of the entire original-physical current.  The
# numerator equality is in QQ(x,y,z)[p], after using only Y²=L²−4p⁶.
divtotal=rat(sum(s.diff(Ktotal[i],xx[i]) for i in range(3)))
remainder=-divtotal
L=H+C*p
Y2=L**2-4*p**6
literal=divtotal*Y2-L*(Ktotal.dot(grad(H))+p*Ktotal.dot(grad(C)))
original=-y**3*L/6
check('WHOLE_ORIGINAL_SOURCE_MINUS_LITERAL_CURVATURE',original-literal-remainder*Y2)
check('exported_entire_remaining_packet',remainder-6*x*y*pull(parent['pure_hol_remaining']))

pt={x:s.Integer(1),y:s.Integer(1),z:s.Integer(1)}
at=lambda v:str(s.cancel(v).subs(pt))
point={'x':'1','y':'1','z':'1','forced_scalar':at(forced),
       'eta':at(eta),'Omega_mass':at(Oscale*mass),'physical_b':at(b),
       'prior_vector':list(map(at,Kprior)),'CM_vector':list(map(at,KCM)),
       'combined_vector':list(map(at,Ktotal)),'remaining':at(remainder)}
assert point['forced_scalar']=='-40/3003',point
assert point['remaining']=='7117189/18729711',point
out={
 'status':'INDEPENDENT_ORIGINAL_PHYSICAL_WHOLE_CURRENT_AUDIT_PASSED_NONZERO_REMAINDER',
 'checks':checks,'check_count':len(checks),
 'coordinates':'u=x³,w=y²/x,q=xy,eta=2x³+y⁶/x³−3z²/4; dx dy dz dp orientation.',
 'original_source':'beta=−y³L dx dy dz dp/(6Y³),L=H+Cp,H=1+z⁶+x⁶+y⁶+zxy/2,C=zx³/2+xy/3,Y²=L²−4p⁶.',
 'construction':'Ktotal=Kprior−b*(Ohat cross Acontact)/[(Ohat cross Acontact) dot gradC]; Jtotal=(K0 dy dz+K1 dz dx+K2 dx dy) wedge dp/Y.',
 'Ohat':list(map(str,Ohat)),'physical_b':str(rat(b)),
 'prior_vector':list(map(str,Kprior)),'CM_vector':list(map(str,KCM)),
 'combined_vector':list(map(str,Ktotal)),
 'forced_scalar':str(forced),'remaining':str(remainder),
 'whole_identity':'beta=dJtotal+remaining*dx dy dz dp/Y; all p/Y³ terms cancel identically under the forced source normalization.',
 'point':point,
 'closure':'The literal remaining coefficient is nonzero. This verifies the one forced candidate and does not supply a full primitive.',
 'elapsed_seconds':round(time.time()-started,3)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'whole original physical audit; remaining',point['remaining'],round(time.time()-started,3),flush=True)
