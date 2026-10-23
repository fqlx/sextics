#!/usr/bin/env python3
"""Exact rational weighted model and chart audit at v^6+1=0.

The original-series provenance is special_P_series.py.  All q,zeta
dependence in its new initial form is removed by unit coordinate changes.
"""
from pathlib import Path
from fractions import Fraction
import json,subprocess
import sympy as s
import yaml
HERE=Path(__file__).resolve().parent
ep,w,b,r,n,zeta,q=s.symbols('eps W b r n zeta q')
data=json.loads((HERE/'special_P_series.json').read_text())
newweights=(1,1,4,2,4)
raw=0
for row in data['rows']:
    wt=row['eps']+4*row['b']+2*row['r']+4*row['nu']
    if wt<=8:
        assert wt==8,row
        raw+=s.sympify(row['coefficient'],locals={'zeta':zeta,'q':q})*ep**row['eps']*b**row['b']*r**row['r']*n**row['nu']
raw_expected=(1225000*q**2*zeta**3*b*b-11576250*q**2*b*r*r
              -4134375*q**2*zeta*ep*ep*b*r+48620250*zeta*n*r*r
              +23152500*zeta*zeta*n*ep*ep*r)
assert s.expand(raw-raw_expected)==0

# B=zeta*b_old, R=r_old/zeta, n=zeta²*nu_old/q².
G=s.cancel(raw.subs({b:b/zeta,r:zeta*r,n:q*q*n/zeta**2},simultaneous=True)
           /(1225000*q*q*zeta))
G=s.expand(G)
expected_G=b*b-s.Rational(189,20)*b*r*r-s.Rational(27,8)*ep*ep*b*r+n*(s.Rational(3969,100)*r*r+s.Rational(189,10)*ep*ep*r)
assert s.expand(G-expected_G)==0
c=s.Rational(5,7)
F=w**6+c*w**3*ep**3+b*(r+c*ep**2)
rec=yaml.safe_load(Path('/workspace/sextics/data/cyclic-triple-residual/instance.rec').read_text())
rawF=0
for co,ex in rec['polynomialData']['F']['terms']:
 for j in range(3):
  for k in range(2):
   ie,iw,ib,ir,inu=ex[0]+ex[1],ex[2],ex[4]+j,j,k
   wt=ie+iw+4*ib+2*ir+4*inu
   if wt>6:continue
   cf=s.Rational(co)*s.binomial(s.Rational(ex[3],6),j)*s.binomial(s.Rational(ex[1],6),k)*(-1)**(j+k)
   zq,zr=divmod(ex[3]-ex[1],6)
   cf*=s.Integer(-1)**zq
   rawF+=cf*zeta**zr*q**(ex[1]%6)*ep**ie*w**iw*b**ib*r**ir*n**inu
newF=s.cancel(rawF.subs({b:b/zeta,r:zeta*r,n:q*q*n/zeta**2},simultaneous=True))
assert s.expand(newF-F)==0
assert {sum(ei*wi for ei,wi in zip(e,newweights)) for e in s.Poly(F,ep,w,b,r,n).monoms()}=={6}
assert {sum(ei*wi for ei,wi in zip(e,newweights)) for e in s.Poly(G,ep,w,b,r,n).monoms()}=={8}

# Exact QQ projective singular-locus and inherited-axis quasismoothness.
singular=r'''ring R=0,(e,w,b,r,n),dp;
poly F=w6+5/7*w3*e3+b*(r+5/7*e2);
poly G=b2-189/20*b*r2-27/8*e2*b*r+n*(3969/100*r2+189/10*e2*r);
ideal I=F,G; ideal J=I+minor(jacob(I),2);
"FULL_DIM";dim(std(J));
ideal Je=std(subst(J,e,1)); "E_CHART";Je;
ring S=0,(e,w,b,r),dp;
poly F=w6+b*(r+5/7*e2);
poly G=b2+3969/100*r2+189/10*e2*r;
ideal J=std(ideal(F,G)+minor(jacob(ideal(F,G)),2));
"OLD_DIM";dim(J);"OLD_COLENGTH";vdim(J);exit;
'''
(HERE/'special_P_audit.sing').write_text(singular)
proc=subprocess.run(['/workspace/research/tools/algebra/bin/Singular','-q',str(HERE/'special_P_audit.sing')],capture_output=True,text=True,check=True,timeout=30)
(HERE/'special_P_audit.log').write_text(proc.stdout+proc.stderr)
lines=proc.stdout.splitlines()
assert int(lines[lines.index('FULL_DIM')+1])==1
assert int(lines[lines.index('OLD_DIM')+1])==0
assert int(lines[lines.index('OLD_COLENGTH')+1])==83

# A direct rational elimination of b on e=1 except r=-c.
K=w**3*(w**3+c)
ar=s.Rational(3969,100);dr=s.Rational(189,10)
p=(r+c)*r*(s.Rational(189,20)*r+s.Rational(27,8))
g=(r+c)**2*r*(ar*r+dr)
H=s.expand(K*K+p*K+n*g)
assert s.cancel(G.subs({ep:1,b:-K/(r+c)})*(r+c)**2-H)==0
r0=s.Rational(0);r1=-dr/ar
assert r1==-s.Rational(10,21)
assert s.diff(g,r).subs(r,r0)!=0 and s.diff(g,r).subs(r,r1)!=0
assert p.subs(r,r0)==0 and p.subs(r,r1)==s.Rational(25,196)
# Splitting lemma in (r,n): g has a simple zero at either r_i,
# so the residual one-variable germ is H(w,r_i,n)=K²+p(r_i)K.
# Its exact orders at the four types of w-points determine A_{order-1}.
assert s.Poly(H.subs(r,0),w,n).as_dict()==s.Poly(K*K,w,n).as_dict()
assert s.Poly(K*K,w).terms()[-1][0][0]==6
assert s.Poly((K*K+p.subs(r,r1)*K),w).terms()[-1][0][0]==3
ww=s.symbols('w0')
# At w0³=-c, K has a simple zero; at w0³=-c/2, K is critical,
# but K²+p1*K has nonzero second derivative.
rem=lambda expr,rel:s.rem(s.Poly(s.expand(expr),ww),s.Poly(rel,ww)).as_expr()
assert rem(s.diff(K,w).subs(w,ww),ww**3+c)!=0
assert rem(s.diff(K*K+p.subs(r,r1)*K,w,2).subs(w,ww),ww**3+c/2)!=0
special_n=s.Rational(75,784)
assert rem(H.subs({r:r1,n:special_n,w:ww}),ww**3+c/2)==0
assert rem(s.diff(H,r).subs({r:r1,n:special_n,w:ww}),ww**3+c/2)==0
# At r=-c the other equation eliminates n, leaving K+b*(r+c), A2.
assert (r*(ar*r+dr)).subs(r,-c)!=0

# The only new-weight monomials of weight<3 are the seven below.
# Every one has old weight<8, proving I_old subset I_new by monomials.
small=[]
for ie in range(3):
 for iw in range(3):
  for ib in range(1):
   for ir in range(2):
    for inu in range(1):
     ex=(ie,iw,ib,ir,inu)
     nw=sum(x*y for x,y in zip(ex,newweights))
     if nw<3:
      ow=3*ie+2*iw+6*ib+6*ir
      assert ow<8
      small.append({'exponent':ex,'new_weight':nw,'old_weight':ow})

# Actual source in these normalized coordinates.  From source_transition:
# source=-eps^4*b_old/(6*a²) deps dW db_old dr_old dv.
# dv/dnu=1/(6v0^5), v0=q/zeta.  Its initial unit becomes -q^-3/36.
source_unit=s.cancel(-q*q/(36*zeta**5*(q/zeta)**5))
assert source_unit==-1/(36*q**3)

report={
 'original_D_series_sha_bound_in':'special_P_series.json',
 'point':'a0^6=-1,v0^6=-1; q=a0*v0, q^6=1',
 'unit_normalization':'B=a0*b_old, R=r_old/a0, n=a0²*(v^6+1)/q²',
 'initial_F':str(F),'initial_G':str(G),
 'initial_F_independently_extracted_from_pinned_sextic':True,
 'weights':newweights,'degrees':[6,8],'first_discrepancy':sum(newweights)-6-8-1,
 'all_initial_coefficients_rational':True,
 'projective_singularities':[
  {'e':1,'W':0,'B':0,'R':0,'n':0,'type':'A5','count':1},
  {'e':1,'W_cubic':'W^3=-5/7','B':0,'R':0,'n':0,'type':'A1','count':3},
  {'e':1,'W':0,'B':0,'R':'-5/7','n':0,'type':'A2','count':1},
  {'e':1,'W':0,'B':0,'R':'-10/21','n':0,'type':'A2','count':1},
  {'e':1,'W_cubic':'W^3=-5/14','B':'15/28','R':'-10/21','n':'75/784','type':'A1','count':3},
  {'e':0,'W':0,'B':0,'R':0,'n':1,'type':'inherited generic corner; mu4 chart','count':1}],
 'inherited_axis_second_weights':[3,2,6,6],
 'inherited_axis_initial_F':'W^6+B*(R+5*eps^2/7)',
 'inherited_axis_initial_G':'B^2+3969*R^2/100+189*eps^2*R/10',
 'inherited_axis_exact_QQ_jacobian_dimension':0,
 'inherited_axis_exact_QQ_jacobian_colength':83,
 'new_low_weight_monomials':small,
 'old_adjoint_ideal_implies_first_new_valuation':True,
 'actual_source_initial_numerator':'-q^(-3)*eps^4*B/36',
 'actual_source_new_weight':8,'actual_source_radial_exponent_over_F_squared':7,
 'scope':'Exact formal initial models, chart singularity ADE classification, and valuation comparison. The full adjoint conclusion additionally uses rationality of Du Val deformations and finite quotient singularities; proof in special_P_proof.md.'}
(HERE/'special_P_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
