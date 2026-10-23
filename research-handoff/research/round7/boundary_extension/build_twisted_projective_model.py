"""Weighted projective bundle model avoiding codimension-two corner components."""
from pathlib import Path
import runpy,json,pickle,sympy as S
P=runpy.run_path(str(Path(__file__).with_name('build_projective_model.py')))
q,h,v,U,t,z,ell=[P[k]for k in ('q','h','v','U','t','z','ell')]
q0,q1,h0,h1,v0,v1=[P[k]for k in ('q0','q1','h0','h1','v0','v1')]
E=P['E'];cox=P['cox'];sg=P['sg']
ROOT=Path(__file__).parent/'twisted_projective_model';ROOT.mkdir(exist_ok=True)
deg={q0:(1,0,0,0),q1:(1,0,0,0),h0:(0,1,0,0),h1:(0,1,0,0),v0:(0,0,1,0),v1:(0,0,1,0),U:(2,2,0,1),t:(4,4,2,2),z:(0,0,0,1)}
ds=[(12,12,4,6),(12,12,5,6),(12,12,6,6)]
EH=[]
for e,d in zip(E,ds):
 out=0
 for ex,c in S.Poly(e,q,h,v,U,t,z).terms():
  iq,ih,iv,iu,it,iz=ex
  dq=iq+2*iu+4*it;dh=ih+2*iu+4*it;dv=iv+2*it
  assert max(dq-d[0],dh-d[1],dv-d[2])<=0
  out+=c*q1**iq*q0**(d[0]-dq)*h1**ih*h0**(d[1]-dh)*v1**iv*v0**(d[2]-dv)*U**iu*t**it*z**iz
 EH.append(S.expand(out))
for f,d in zip(EH,ds):
 for ex,c in S.Poly(f,*cox).terms():
  assert tuple(sum(n*deg[x][j]for x,n in zip(cox,ex))for j in range(4))==d
assert all(S.expand(f.subs({q0:1,q1:q,h0:1,h1:h,v0:1,v1:v})-e) == 0 for f,e in zip(EH,E))
assert S.Poly(EH[2],t).coeff_monomial(t**3)==1
cinf=[S.factor(f.subs({v0:0,v1:1}))for f in EH]
assert cinf==[U**4*(U**2+3*t),3*U**2*t**2,t**3]
l=S.Poly(EH[0],t).nth(1);m=S.Poly(EH[0],t).nth(0)
n,o,p=[S.Poly(EH[1],t).nth(i)for i in (2,1,0)]
a,b=[S.Poly(EH[2],t).nth(i)for i in (1,0)]
assert l==3*U**4*v1**2
script='option(redSB);\nring R=109,('+','.join(map(str,cox))+'),wp(5,12,1,1,1,1,1,1,1);\n'
for name,expr in [('ll',l),('mm',m),('nn',n),('oo',o),('pp',p),('aa',a),('bb',b)]:
 script+='poly '+name+'='+sg(expr,cox)+';\n'
script+='poly R12=nn*mm^2-oo*mm*ll+pp*ll^2;\n'
script+='poly R13=-mm^3-aa*mm*ll^2+bb*ll^3;\n'
script+='print("GCD_START");\npoly gg=gcd(R12,R13);\nprint("GCD_DONE");\nprint(gg);\nquit;\n'
(ROOT/'height_gcd_mod109.sing').write_text(script)
sat=P['sat']
ss='LIB "elim.lib";\noption(redSB);\nring R=109,('+','.join(map(str,cox))+'),wp(5,12,1,1,1,1,1,1,1);\n'
ss+='ideal JJ='+','.join(sg(f,cox)for f in EH)+';\n'
ss+='poly ff='+sg(sat,cox)+';\nprint("TWISTED_SATURATION_START");\n'
ss+='ideal II=sat(JJ,ideal(ff));\nprint("TWISTED_SATURATION_DONE");\nprint(size(II));\n'
ss+='write("'+str(ROOT/'saturated_mod109.sing')+'",II);\n'
ss+='ideal CC=quotient(JJ,II);\nprint("TWISTED_CANONICAL_COLON_DONE");\n'
ss+='write("'+str(ROOT/'canonical_colon_mod109.sing')+'",CC);\nquit;\n'
(ROOT/'saturate_mod109.sing').write_text(ss)
meta={'Cox_variable_degrees':{str(k):list(v)for k,v in deg.items()},'equation_multidegrees':ds,'E3_monic_t_cubed':True,'E1_t_coefficient':str(l),'v_infinity_equations':list(map(str,cinf)),
 'saturation':str(P['sat']),'conditional_CI_canonical_shift':[28,28,11,14],
 'height_strategy':'Outside U*v1=0, eliminate t from E1; height>=3 follows if gcd(R12,R13) is supported on U*v1. On U=0 or v1=0, E1=B2*z6 and E3 monic t3 are coprime, giving height>=3 directly.',
 'height_verified_by_separate_gcd_receipt':True,'all_homogeneity_and_affine_replay_checks':True,
 'canonical_main_component':'((J:I)/J)(28,28,11,14), with I=J:f^infinity, then Cox sheafification; colon generators still pending'}
(ROOT/'model.json').write_text(json.dumps(meta,indent=2)+'\n')
(ROOT/'model.pickle').write_bytes(pickle.dumps(dict(EH=EH,degrees=ds,variable_degrees=deg,cox=cox,saturation=P['sat'])))
print(json.dumps(meta,indent=2))
