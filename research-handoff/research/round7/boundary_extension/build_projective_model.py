"""Construct and verify the saturated incidence compactification input.

The output includes a full Cox ideal and a separate good generic-fiber check.
No claim is made that the global saturation/Groebner calculation terminates.
"""
from pathlib import Path
import pickle,json,sympy as S

ROOT=Path(__file__).parent/'projective_model'
ROOT.mkdir(exist_ok=True)
P=pickle.load(open('/workspace/research/round7/moving_j1728/legendre_model.pickle','rb'))
q,h=[P['symbols'][x] for x in ('q','h')]
ell=S.symbols('ell')
U,t,z,v=S.symbols('U t z v')
q0,q1,h0,h1,v0,v1=S.symbols('q0 q1 h0 h1 v0 v1')
a1,a0,b2,b1,b0=[P['coefficients'][x] for x in ('a1','a0','b2','b1','b0')]
E=[
 b2*z**6+a1*v*U**2*z**4+3*v**2*U**4*t+v**2*U**6*(v**2+1+4*ell),
 a1*t*z**4+b1*z**6+v*U**2*(3*t*t+a0*z**4)-v*U**6*((8*ell-4)*v*v+8*ell),
 t**3+a0*t*z**4+b0*z**6+U**6*(4*ell+(8*ell-4)*v*v+(4*ell-4)*v**4)]
degrees=[(12,8,4,6),(6,7,3,6),(12,6,4,6)]
def homogenize(f,d):
 out=0
 for ex,cf in S.Poly(S.expand(f),q,h,v,U,t,z).terms():
  iq,ih,iv,iu,it,iz=ex
  assert iu+2*it+iz==d[3]
  out+=cf*q1**iq*q0**(d[0]-iq)*h1**ih*h0**(d[1]-ih)*v1**iv*v0**(d[2]-iv)*U**iu*t**it*z**iz
 return S.expand(out)
EH=[homogenize(e,d)for e,d in zip(E,degrees)]
affine={q0:1,q1:q,h0:1,h1:h,v0:1,v1:v,z:1}
assert all(S.expand(eh.subs(affine)-e.subs(z,1)) == 0 for eh,e in zip(EH,E))
cox=(U,t,z,v1,v0,h1,h0,q1,q0)
degv={q0:(1,0,0,0),q1:(1,0,0,0),h0:(0,1,0,0),h1:(0,1,0,0),v0:(0,0,1,0),v1:(0,0,1,0),U:(0,0,0,1),t:(0,0,0,2),z:(0,0,0,1)}
for f,d in zip(EH,degrees):
 for ex,cf in S.Poly(f,*cox).terms():
  assert tuple(sum(a*degv[x][j]for a,x in zip(ex,cox))for j in range(4))==d

def sg(f,vars,prime=109,ep=46):
 f=S.expand(f.subs(ell,ep))
 out=[]
 for ex,cf in S.Poly(f,*vars).terms():
  cf=S.Rational(cf);c=int(cf.p)%prime*pow(int(cf.q)%prime,-1,prime)%prime
  if not c:continue
  mons='*'.join(str(x)+(f'^{n}' if n > 1 else '') for x,n in zip(vars,ex) if n)
  out.append(str(c)+('*'+mons if mons else''))
 return '+'.join(out)or'0'
sat=q0*h0*v0*h1*(h1*h1-4*h0*h0)*v1*U*z*(v1*v1-v0*v0)*(v1*v1-ell*v0*v0)
header='LIB "elim.lib";\noption(redSB);\n'
glob=header+'ring R=109,('+','.join(map(str,cox))+'),dp;\n'
glob+='ideal JJ='+','.join(sg(f,cox)for f in EH)+';\n'
glob+='poly ff='+sg(sat,cox)+';\n'
glob+='print("GLOBAL_SATURATION_START");\n'
glob+='ideal II=sat(JJ,ideal(ff));\n'
glob+='print("GLOBAL_SATURATION_DONE");\nprint(size(II));\nprint(dim(std(II)));\n'
glob+='write("'+str(ROOT/'saturated_mod109.sing')+'",II);\n'
glob+='print("SATURATION_READY_FOR_CANONICAL_EXT");\nquit;\n'
(ROOT/'global_mod109.sing').write_text(glob)
fvars=(U,t,v)
fiber=header+'ring R=109,(U,t,v),dp;\n'
fiber+='ideal JJ='+','.join(sg(f.subs({q:2,h:5,z:1}),fvars)for f in E)+';\n'
fiber+='ideal II=sat(JJ,ideal(U*v*(v*v-1)*(v*v-46)));\n'
fiber+='ideal GG=std(II);\nprint("FIBER_DIMENSION");\nprint(dim(GG));\nprint(vdim(GG));\n'
fiber+='ideal jac=minor(jacob(II),3);\nprint("FIBER_SINGULAR_LOCUS_DIMENSION");\nprint(dim(std(II+jac)));\nquit;\n'
(ROOT/'fiber_mod109.sing').write_text(fiber)
avars=(U,t,v,h,q)
aff=header+'ring R=109,('+','.join(map(str,avars))+'),dp;\n'
aff+='ideal JJ='+','.join(sg(f.subs(z,1),avars)for f in E)+';\n'
aff+='print("AFFINE_MAIN_SATURATION_START");\n'
aff+='ideal II=sat(JJ,ideal(h*(h*h-4)*v*U));\n'
aff+='print("AFFINE_MAIN_SATURATION_DONE");\nprint(size(II));\nprint(dim(std(II)));\n'
aff+='write("'+str(ROOT/'affine_saturated_mod109.sing')+'",II);\nquit;\n'
(ROOT/'affine_mod109.sing').write_text(aff)
cvars=(U,t,v,h)
curve=header+'ring R=109,(U,t,v,h),dp;\n'
curve+='ideal JJ='+','.join(sg(f.subs({q:2,z:1}),cvars)for f in E)+';\n'
curve+='print("Q2_CURVE_SATURATION_START");\n'
curve+='ideal II=sat(JJ,ideal(h*(h*h-4)*v*U));\n'
curve+='print("Q2_CURVE_SATURATION_DONE");\nprint(size(II));\nprint(dim(std(II)));\n'
curve+='write("'+str(ROOT/'q2_curve_saturated_mod109.sing')+'",II);\n'
curve+='ideal CC=quotient(JJ,II);\nprint("Q2_CURVE_CANONICAL_COLON_DONE");\n'
curve+='write("'+str(ROOT/'q2_curve_canonical_colon_mod109.sing')+'",CC);\nquit;\n'
(ROOT/'q2_curve_mod109.sing').write_text(curve)
meta={'ambient':'P1_q x P1_h x P1_v x WP(1_U,2_t,1_z)', 'equation_multidegrees':degrees,
 'canonical_CI_shift':[28,19,9,14],
 'saturation':str(sat),'correct_main_component':'I=(E1,E2,E3):saturation^infinity',
 'canonical_module_formula':'Ext^3_R(R/I,R)(-2,-2,-2,-4), after saturation and Cox sheafification; resolution generators pending',
 'canonical_caveat':'The raw equations have codimension-two boundary components q0=v0=0 and h0=v0=0, so J is not a global CI. The displayed CI shift is only a formal degree sum and is NOT the canonical module. CI linkage may only be used on a verified height-three open.',
 'homogeneity_verified':True,'affine_equations_replayed':True,'term_counts':[len(S.Poly(f,*cox).terms())for f in EH],
 'character':'U -> -U; all equations and saturation ideal invariant',
 'generic_fiber':{'prime':109,'ell':46,'q':2,'h':5}}
(ROOT/'model.json').write_text(json.dumps(meta,indent=2)+'\n')
(ROOT/'model.pickle').write_bytes(pickle.dumps(dict(E=E,EH=EH,cox=cox,degrees=degrees,saturation=sat)))
print(json.dumps(meta,indent=2))
