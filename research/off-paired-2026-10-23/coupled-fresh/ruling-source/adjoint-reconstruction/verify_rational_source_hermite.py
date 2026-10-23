"""Exact source-specific rational Hermite and boundary connection checks."""
import json
from pathlib import Path
import sympy as s
i,J,w=s.symbols('i J w',nonzero=True)
T=1+w**3
N=9*i*i*w*w-16*J*T
k=3*i*w/(4*T)
A=k*k*T/J
R=A-1
S=k**6/R
delta=3*R*S*w**3-3*R*S-8*R*w**3+R-S*w**3+2*S
h=3*i*w**3/(32*J*T*T*delta)
v=w**3/(64*T**4*A*(1+S))
Rsource=54*i**3*w*T/(J*N)
checks=[]
def check(name,f):
 assert s.cancel(f)==0,name
 checks.append(name)
check('actual physical density transport',h*s.diff(v,w)/v**2-Rsource)
M=256*T**5*N+729*i**6*J*w**6
check('factored rational v',v-64*J*w*N*T*T/(9*i*i*M))
P=-27*i**3*w*w/(16*J*J)-243*i**5*w/(128*J**3)
Q=2187*i**7*w*w/(128*J**3)-243*i**5/(8*J*J)
check('complete Hermite division',Rsource-s.diff(P,w)-Q/N)
check('source-weight identity',i*s.diff(Rsource,i)+2*J*s.diff(Rsource,J)+Rsource)

Jroot=9*i*i*w*w/(16*T)
residue=32*T**3/(3*i*w*w*(2-w**3))
check('finite N residue',
 (54*i**3*w*T/(J*s.diff(N,w))).subs(J,Jroot)-residue)
u=9*w*w/(16*T)
check('inverse-root moment in u',residue*i*s.diff(u,w)-6*(1/w+w*w))

# Fixed J: i^2=16 J T/(9w^2), so di/dw=i(w^3-2)/(2wT).
di_dw=i*(w**3-2)/(2*w*T)
R1=s.Rational(8,3)/w**2-s.Rational(32,3)*w-s.Rational(4,3)*w**4
check('rational transverse residue primitive',residue*di_dw-s.diff(R1,w))

# The next moment is a third-kind form on y^2=T; its retained logarithmic
# derivative is rational on that curve.  This is an identity, not a primitive
# of the original curve-valued source.
y=s.symbols('y',nonzero=True)
dy_dw=3*w*w/(2*y)
dlog=(dy_dw/(y-1)-dy_dw/(y+1))
num=s.cancel(dlog-3/(w*y)).as_numer_denom()[0]
assert s.rem(num,y*y-T,y)==0
checks.append('retained elliptic third-kind differential')

out={'status':'exact source-specific Hermite reduction, no primitive claimed',
 'checks':checks,'count':len(checks),
 'Rsource':str(Rsource),'polynomial_primitive':str(P),
 'proper_numerator':str(Q),'proper_denominator':str(N),
 'N_residue':str(residue),'transverse_primitive':str(R1),
 'retained_logarithms':'r du=6 dlog(w)+2 d(w^3); the second transverse moment has the stated elliptic dlog component',
 'scope':'Density/relative scalar residues only. Every operator, curve connection, other pole and (Z-1) remainder must still be served.',
 'certificate':False}
Path(__file__).with_name('rational-source-hermite-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact actual-source Hermite and boundary checks')
