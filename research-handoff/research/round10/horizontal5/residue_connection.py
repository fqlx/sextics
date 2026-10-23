#!/usr/bin/env python3
"""Independent rank-two finite-point residue connection for the open Prym curve.

The third-kind generators sigma_j=W^(3j)dW/((t-s)C_t) have residues
r0=-1/C_W andr1=-W^3/C_W. This computes their algebraic variation before
the properrank3 extension is assembled, without any Griffiths reductions.
"""
import json,pickle,time
from pathlib import Path
from native_rf import RF,zero,one,flatness
HERE=Path(__file__).resolve().parent;start=time.time()
L,r,x,s=[RF(t) for t in ('L','r','x','s')];c=RF('5/7');q=c*(1+s);p=L+r*s+s**3/x
class QF:
    def __init__(self,a=0,b=0):self.a=RF(a);self.b=RF(b)
    def __add__(a,b):
        if not isinstance(b,QF):b=QF(b)
        return QF(a.a+b.a,a.b+b.b)
    __radd__=__add__
    def __neg__(a):return QF(-a.a,-a.b)
    def __sub__(a,b):return a+-b if isinstance(b,QF) else a+(-RF(b))
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,QF):b=QF(b)
        return QF(a.a*b.a-p*a.b*b.b,a.a*b.b+a.b*b.a-q*a.b*b.b)
    __rmul__=__mul__
    def inv(a):
        norm=a.a**2-q*a.a*a.b+p*a.b**2
        return QF((a.a-q*a.b)/norm,-a.b/norm)
    def __truediv__(a,b):return a*(b.inv() if isinstance(b,QF) else QF(b).inv())
    def __rtruediv__(a,b):return QF(b)*a.inv()
u=QF(0,1);D=2*u+q;out={};theta_checks={}
for v in ('L','r','x','s'):
    uj=-(u*q.diff(v)+p.diff(v))/D
    logr0=-(2*uj/u)/3-(2*uj+q.diff(v))/D
    row1=uj+u*logr0
    out[v]=[[logr0.a,logr0.b],[row1.a,row1.b]]
    g=[-u-q,QF(-1)]
    derivative=[-uj-q.diff(v),QF(0)]
    for i in range(2):
        horizontal=derivative[i]+(uj/u)*RF('2/3')*g[i]+sum((g[k]*out[v][k][i] for k in range(2)),QF(0))
        assert not horizontal.a and not horizontal.b,('theta horizontal',v,i)
    theta_checks[v]=True
checks=flatness(out);assert not any(checks.values())
packet={'variables':('L','r','x','s'),'quadratic_u':{'q':q.json(),'p':p.json()},'residue_basis':('-1/C_W','-W^3/C_W'),'boundary_generators':('dW/((t-s)C_t)','W^3*dW/((t-s)C_t)'),
        'theta_projection':'theta_chi=(1-zeta3^2)*w^2*((-q-u)*sigma0-sigma1), u=w^3, q=c*(1+s)',
        'theta_residue_coefficient_horizontal_exact':theta_checks,
        'theta_proper_derivative':'(1-zeta3^2)*w^2*((-q-u)*N_j[3,0:3]-N_j[4,0:3])',
        'connection':{v:[[z.json() for z in row] for row in mat] for v,mat in out.items()},'exact_flatness':checks,'convention':'rows are basis derivatives; coefficient columns transpose','seconds':time.time()-start}
pickle.dump(packet,open(HERE/'residue_connection.pickle','wb'));(HERE/'residue_connection.json').write_text(json.dumps(packet,indent=2));print(json.dumps({'exact_flatness_zero':not any(checks.values()),'seconds':time.time()-start},indent=2))
