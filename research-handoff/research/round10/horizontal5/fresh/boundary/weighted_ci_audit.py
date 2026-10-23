#!/usr/bin/env python3
"""Audit the actual D32 weighted initial CI at a conductor/Fermat corner.

Coordinates: Y2=1, X0=eps, X1=v*eps, X2=W, Y1=b,
delta=Y0**6+1, delta=b*r, Y0=zeta*(1-delta)**(1/6).
The fixed relation is zeta**6=-1.  This script derives the initial form
from the original 558-term D, rather than trusting a rescaled Taylor file.
"""
import hashlib
import json
import pathlib
import pickle
import subprocess
import sympy as s

HERE = pathlib.Path(__file__).resolve().parent
SOURCE = pathlib.Path('/workspace/research/round9/abel_prym/effective_graph.pickle')
zeta, v, eps, b, r, W = s.symbols('zeta v eps b r W')
packet = pickle.loads(SOURCE.read_bytes())

def red(expr):
    return s.rem(s.Poly(s.expand(expr), zeta), s.Poly(zeta**6+1, zeta)).as_expr().expand()

def coefficient(radial, bexp, dexp):
    return red(sum(s.Rational(c)*(-1)**dexp*s.binomial(s.Rational(e[3],6),dexp)
                   *zeta**e[3]*v**e[1]
                   for e,c in packet['D'].items()
                   if e[0]+e[1]==radial and e[4]==bexp))

initial = 0
low_terms = []
for radial in (17,19):
    ep = radial-17
    for bexp in range(5):
        for dexp in range(3):
            # After delta=b*r and division by b**2.
            wt = 3*ep+6*bexp+12*dexp-12
            if wt > 12:
                continue
            c = coefficient(radial,bexp,dexp)
            if not c:
                continue
            if wt < 12:
                low_terms.append((ep,bexp,dexp,str(c)))
            initial += c*eps**ep*b**(bexp+dexp-2)*r**dexp
assert not low_terms, low_terms
initial=s.expand(initial)
old=json.loads((HERE/'blowup_quadratic.json').read_text())
cs={name:s.sympify(old[name],locals={'zeta':zeta,'v':v}) for name in ('A','B','C','D','E')}
expected=cs['A']*r**2+cs['C']*b*r+cs['D']*b**2+eps**2*(cs['B']*r+cs['E']*b)
assert red(initial-expected)==0

# Independent raw-coordinate check of the normal-coordinate scaling.
raw_aa=red(sum(s.Integer(c)*s.binomial(e[3],2)*zeta**(e[3]-2)*v**e[1]
               for e,c in packet['D'].items()
               if e[0]+e[1]==17 and e[4]==0 and e[3]>=2))
assert red(raw_aa-cs['A']*(6*zeta**5)**2)==0

F=W**6+b*(r+s.Rational(5,7)*zeta*eps**2)
report={
    'original_D_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'coordinate':'delta=a^6+1, delta=b*r; a=zeta*(1-delta)^(1/6)',
    'weights':{'eps':3,'W':2,'b':6,'r':6},
    'equation_degrees':[12,12],
    'F_initial':str(F),'D_initial':str(initial),
    'all_lower_weight_terms_vanish':True,
    'five_coefficients_match_packet':True,
    'raw_delta_a_scaling_checked':True,
    'fibers':[]}

def fp(expr, point, p):
    val=s.cancel(expr.subs({zeta:point[0],v:point[1]}))
    nu,de=map(int,s.fraction(val))
    return nu*pow(de,-1,p)%p

for p,zz,vv in [(101,10,2),(101,10,3),(101,10,1)]:
    assert (pow(zz,6,p)+1)%p==0
    cf={name:fp(expr,(zz,vv),p) for name,expr in cs.items()}
    lam=5*pow(7,-1,p)*zz%p
    singular=f'''ring R={p},(eps,W,b,r),dp;
poly F=W^6+b*(r+{lam}*eps^2);
poly D={cf['A']}*r^2+{cf['C']}*b*r+{cf['D']}*b^2+eps^2*({cf['B']}*r+{cf['E']}*b);
ideal I=F,D;
matrix M=jacob(I);
ideal J=I+minor(M,2);
ideal G=std(J);
"JACOBIAN_DIM"; dim(G);
"JACOBIAN_VDIM"; vdim(G);
exit;
'''
    stem=f'ci_p{p}_z{zz}_v{vv}'
    path=HERE/(stem+'.sing');path.write_text(singular)
    result=subprocess.run(['/workspace/research/tools/algebra/bin/Singular','-q',str(path)],
                          capture_output=True,text=True,timeout=35)
    (HERE/(stem+'.log')).write_text(result.stdout+result.stderr)
    out=result.stdout.splitlines()
    jd=int(out[out.index('JACOBIAN_DIM')+1]);jv=int(out[out.index('JACOBIAN_VDIM')+1])
    row={'p':p,'zeta':zz,'v':vv,'coefficients':cf,'lambda':lam,
         'jacobian_dimension':jd,'jacobian_colength':jv,
         'quasismooth':jd==0,'returncode':result.returncode}
    report['fibers'].append(row)
    assert jd==0,row
    break

(HERE/'weighted_ci_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('all_lower_weight_terms_vanish','five_coefficients_match_packet','raw_delta_a_scaling_checked','fibers')},indent=2))
