"""Exact rank-two background elliptic connection and fiber primitives."""
import json
from pathlib import Path
import sympy as s

q,A,B,D=s.symbols('q A B D')
f=A*q**3+B*q+D
unknown=s.symbols('a b r0 r1 r2')
aa,bb,r0,r1,r2=unknown
R=r0+r1*q+r2*q*q
rhs=(aa+bb*q)*f+s.diff(R,q)*f-R*s.diff(f,q)/2
out={'meaning':'Derivative of omega_j=q^j dq/y equals columns dot(omega0,omega1)+d(R/y), y^2=Aq^3+Bq+D; A fixed',
     'physical_substitution':{'Eplus':'A=2','Eminus':'A=-2','B':'-z/2','D':'H-1-z^6',
                              'M_H':'M_D','M_z':'-M_B/2-6z^5*M_D'},
     'parameters':{}}
matrices={}
count=0
for par,power in [('D',0),('B',1)]:
    cols=[]
    prims=[]
    numeric_cols=[]
    for j in range(2):
        target=-q**(j+power)/2
        sol=s.solve(s.Poly(rhs-target,q).all_coeffs(),unknown)
        vals=[s.factor(sol[t]) for t in unknown]
        assert s.cancel((rhs-target).subs(sol))==0
        count+=1
        cols.append([str(v) for v in vals[:2]])
        numeric_cols.append(s.Matrix(vals[:2]))
        prims.append(str(s.factor(sum(vals[k+2]*q**k for k in range(3)))))
    matrices[par]=s.Matrix.hstack(*numeric_cols)
    out['parameters'][par]={'columns':cols,'primitives_R':prims}

MD,MB=matrices['D'],matrices['B']
flat=MB.diff(D)-MD.diff(B)+MD*MB-MB*MD
assert flat.applyfunc(s.cancel)==s.zeros(2)
count+=1
assert (4*B*MB+6*D*MD-s.diag(-1,1)).applyfunc(s.cancel)==s.zeros(2)
count+=1

# Actual physical parameter Euler field, common to both Eplus and Eminus.
H,z=s.symbols('H z')
DD=H-1-z**6
for aval in (2,-2):
    sub={A:aval,B:-z/2,D:DD}
    MH=MD.subs(sub)
    Mz=(-MB/2-6*z**5*MD).subs(sub)
    assert (6*(H-1+3*z**6)*MH+4*z*Mz-s.diag(-1,1)).applyfunc(s.cancel)==s.zeros(2)
    count+=1

root=Path(__file__).resolve().parent
(root/'background-elliptic-connection.json').write_text(json.dumps(out,indent=2)+'\n')
result={'status':'passed','exact_symbolic_groups':count,
        'scope':'Four fiber reductions, flatness and universal/physical Euler identities. No endpoint source primitive.'}
(root/'background-elliptic-connection-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
