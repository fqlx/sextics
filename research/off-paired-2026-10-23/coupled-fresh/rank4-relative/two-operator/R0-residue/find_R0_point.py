import sympy as s,json
from pathlib import Path
a,z,C=s.symbols('a z C')
K=3*a*z+12*z**5;M=-18*a**3+54*a*z**6
E=s.Rational(1,2)-9*(K**4-3*K*K*M+M*M)/a
F=6*z**5-s.Rational(3,4)*a*z-9*(K**3*M-2*K*M*M)/a
R=s.factor(F*F-K*E*F+M*E*E)
print('R0 factorization:',R,flush=True)
p=1009
Rn,Rd=s.fraction(R)
Ra=s.diff(R,a);Rz=s.diff(R,z)
q=3*C-s.Rational(3,2)*a*z
H=a*a+q**6/(a*a)+z**6+q*z/2+1
Ha=s.diff(H,a);Hz=s.diff(H,z);h=s.diff(H,C)
A=s.cancel(Hz*Ra-Ha*Rz);B=s.diff(A,C)
N=3*H-2*C*h;Delta=4*C**6-729*H**4
# Find one geometric divisor point by factoring successive vertical slices.
def ev(expr,pt):
 n,d=s.fraction(s.cancel(expr));nn=int(n.subs(pt))%p;dd=int(d.subs(pt))%p
 if dd==0:return None
 return nn*pow(dd,-1,p)%p
found=False
for aa in range(1,9):
 pol=s.Poly(Rn.subs(a,aa),z,modulus=p)
 facs=s.factor_list(pol)[1]
 roots=[]
 for fac,mul in facs:
  if fac.degree()==1:
   co=fac.all_coeffs();roots.append((-int(co[1])*pow(int(co[0])%p,-1,p))%p)
 print('a=',aa,'rational roots:',roots,flush=True)
 for zz in roots:
  pt={a:aa,z:zz,C:1}
  vals={name:ev(expr,pt)for name,expr in [('R0',R),('Ra',Ra),('Rz',Rz),('A',A),('B',B),('H',H),('N',N),('Delta',Delta),('q',q),('Ha',Ha),('Hz',Hz),('h',h),('r',N/(3*H))]}
  if vals['R0']==0 and (vals['Ra']or vals['Rz']) and all(vals[k] not in (0,None)for k in ('A','B','H','N','Delta')):
   out={'prime':p,'point':{'a':aa,'z':zz,'C':1},'values':vals,'R0_factorization':str(R)}
   print('POINT',out,flush=True)
   Path('/workspace/off-paired-research-new/coupled-fresh/rank4-relative/two-operator/R0-residue/R0-point.json').write_text(json.dumps(out,indent=2)+'\n')
   found=True;break
 if found:break
if not found:print('No eligible point in these slices; no exclusion claim.')
