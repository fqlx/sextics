"""Lower-degree open smoothness probe on the 27-cover, without sqrt(r)."""
from pathlib import Path
import sympy as S
q,h,f,J,s,t,v,e=S.symbols('q h f J s t v ell')
r=h*h-4
a1=3*J*h/2
a0=-S.Rational(1,3888)-h*q*f*f/2
b2=h*(q**3/8-27*J*J*h/4)
b1=h*(q*q*f/12+5*J/216)
b0=S.Rational(1,629856)+h*q*f*f/216-J*h*h*f**3
c2=3*s*s*t+a1*s+b2
c1=3*s*t*t+a1*t+a0*s+b1
c0=t**3+a0*t+b0
E=[v*c2+s**3*(v*v+1+4*e),v*v*c1-s**3*((8*e-4)*v*v+8*e),v**3*c0+4*s**3*(v*v+1)*((e-1)*v*v+e)]
vars=(s,t,v,f,J,h,q)
def sg(expr):
 out=[]
 for ex,cf in S.Poly(S.expand(expr.subs(e,46)),*vars).terms():
  cf=S.Rational(cf);a=int(cf.p)%109*pow(int(cf.q)%109,-1,109)%109
  if not a:continue
  m='*'.join(str(x)+(f'^{n}' if n>1 else '')for x,n in zip(vars,ex)if n)
  out.append(str(a)+('*'+m if m else''))
 return '+'.join(out)or'0'
p=Path(__file__).parent/'projective_model'
script='LIB "elim.lib";\nring R=109,(s,t,v,f,J,h,q),dp;\n'
script+='ideal EE='+','.join(sg(a)for a in E)+';\n'
script+='poly rr=h*h-4;\nideal rels=4*f*rr-q*q,J-1-q^6;\n'
script+='matrix MM[3][5];\nint i;\nfor(i=1;i<=3;i++){MM[i,1]=diff(EE[i],s);MM[i,2]=diff(EE[i],t);MM[i,3]=diff(EE[i],v);MM[i,4]=2*rr*diff(EE[i],q)+q*diff(EE[i],f)+12*rr*q^5*diff(EE[i],J);MM[i,5]=rr*diff(EE[i],h)-2*h*f*diff(EE[i],f);}\n'
script+='ideal jac=minor(MM,3);\nprint("UNSCALED_OPEN_JAC_START");\n'
script+='ideal SS=sat(EE+rels+jac,ideal(h*rr*s*v*(v*v-1)*(v*v-46)));\n'
script+='print("UNSCALED_OPEN_JAC_DONE");\nprint(dim(std(SS)));\nprint(size(SS));\n'
script+='write("'+str(p/'unscaled_open_singular_ideal_mod109.sing')+'",SS);\nquit;\n'
(p/'unscaled_open_singular_mod109.sing').write_text(script)
