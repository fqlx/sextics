"""Two elliptic companions carry the ENTIRE new literal source density.
All k/t/source-unit and fixed-C endpoint normals are retained.
This is source transport, not a global primitive or Gysin conclusion.
Elliptic quotient formulas supplied by fresh_algebraic_construction.
"""
import sympy as s,json
from pathlib import Path
u,w,q,J,z,k=s.symbols('u w q J z k',nonzero=True)
alpha=3*z*z/4;b=1+z**6
eta=2*u+w**3-alpha
B=alpha*alpha+4*(J-b)
ru=u*u+(w**3-alpha)*u+b-J
rq=q*q-u*w
rk=k**6-B
G=s.groebner([rq,ru,rk],q,u,k,domain=s.QQ.frac_field(w,J,z))
checks={}
def red(f):
    num=s.cancel(f).as_numer_denom()[0]
    return s.factor(G.reduce(num)[1])
def ck(n,f):
    r=red(f);checks[n]=r==0
    assert r==0,(n,r)
C=u*z/2+q/3
E=2*u-2*w**3-alpha-9*z*q*w*w
Nu=1/E;Nw=-(w+3*z*q)/(u*E);Nq=-3*z/(2*E)
Nk=2/(3*k**5)

def N(f):
    return s.diff(f,J)+Nu*s.diff(f,u)+Nw*s.diff(f,w)+Nq*s.diff(f,q)+Nk*s.diff(f,k)
ck('fixed_C_normal_companion_curve',N(ru))
ck('fixed_C_normal_quadratic_branch',N(rq))
ck('fixed_C_normal_scale_cover',N(rk))
ck('fixed_C_normal_actual_C',N(C))
ck('fixed_C_normal_J',N(J)-1)
ck('fixed_C_normal_z',N(z))
x=w/k;v=eta/k**3;t=alpha/k**3
U=x+1/x
Vp=v*(x+1)/x**2;Vm=v*(x-1)/x**2
Ep=lambda VV,sg:VV**2-(U+sg*2)*(U**3-3*U-2*t)
ck('ACTUAL_plus_elliptic_quotient',Ep(Vp,1))
ck('ACTUAL_minus_elliptic_quotient',Ep(Vm,-1))
# Independently total-differentiate each actual elliptic equation.
ck('FULL_plus_elliptic_fixed_C_normal',N(Ep(Vp,1)))
ck('FULL_minus_elliptic_fixed_C_normal',N(Ep(Vm,-1)))
ck('FULL_elliptic_parameter_normal',N(t)+2*t/B)
ck('FULL_source_unit_normal',N(1/k)+2/(3*B*k))
# The absolute one-form has a compulsory moving-k correction.
# For this identity eta can be treated as an independent nonzero coefficient.
ww,kk,yy=s.symbols('ww kk yy',nonzero=True)
xx=ww/kk;vv=yy/kk**3;UU=xx+1/xx
VVp=vv*(xx+1)/xx**2;VVm=vv*(xx-1)/xx**2
cw=s.factor((s.diff(UU,ww)/VVp+s.diff(UU,ww)/VVm)/(2*kk))
ckk=s.factor((s.diff(UU,kk)/VVp+s.diff(UU,kk)/VVm)/(2*kk)+ww*ww/(kk*yy))
checks['ABSOLUTE_companion_sum_dw']=s.factor(cw-ww/yy)==0
checks['ABSOLUTE_companion_sum_dk']=ckk==0
assert checks['ABSOLUTE_companion_sum_dw'] and checks['ABSOLUTE_companion_sum_dk']
# Original physical source density; exact finite source-preserving quotient.
X,Y=s.symbols('X Y',nonzero=True)
uv=X**3;wv=Y*Y/X;qv=X*Y
Jv=1+z**6+uv*uv+uv*wv**3-alpha*uv
Jac=s.factor(s.diff(uv,X)*s.diff(wv,Y)-s.diff(uv,Y)*s.diff(wv,X))
checks['WHOLE_original_density_to_companion']=s.factor(wv*Jac/6-Y**3)==0
assert checks['WHOLE_original_density_to_companion']
# At fixed w,z, du=dJ/eta; retaining all other terms gives the full 3-form.
ck('ACTUAL_companion_u_J',s.diff(ru,u)-eta)
# Fixed-C normal is not partial J at fixed w: it carries every endpoint motion.
pt={u:s.Integer(1),w:s.Integer(1),q:s.Integer(1),J:s.Rational(13,4),z:s.Integer(1)}
ev=lambda f:s.factor(f.subs(pt))
assert ev(ru)==0 and ev(rq)==0 and ev(E)!=0
out={
 'status':'PASS_ACTUAL_WHOLE_SOURCE_TWO_ELLIPTIC_COMPANIONS_AND_ALL_NORMAL_TRANSPORT; PRIMITIVE_OPEN',
 'source_chart':'u=x^3,w=y^2/x,q=xy, q^2=u*w. J=H−3zC/2=1+z^6+u^2+u*w^3−3u*z^2/4, C=u*z/2+q/3.',
 'WHOLE_source_density':'y^3 dx wedge dy wedge dz=w/(6eta) dJ wedge dw wedge dz, eta=2u+w^3−3z^2/4. The quadratic q branch is retained in C and all normals.',
 'companion':'eta^2=(w^3−alpha)^2+4(J−1−z^6), alpha=3z^2/4.',
 'normalization':'B=alpha^2+4(J−1−z^6), k^6=B, x=w/k,v=eta/k^3,t=alpha/k^3.',
 'two_literal_elliptic_maps':'U=x+x^(-1), Vplus=v*(x+1)/x^2, Vminus=v*(x−1)/x^2; Vplus^2=(U+2)(U^3−3U−2t), Vminus^2=(U−2)(U^3−3U−2t).',
 'FULL_absolute_source_differential':'w dw/eta=(dU/Vplus+dU/Vminus)/(2k)+w^2 dk/(k eta). The moving-k term is compulsory.',
 'WHOLE_original_source_density_TWO_CHANNELS':'y^3 dxdy dz=dJ wedge(dU/Vplus+dU/Vminus) wedge dz/(12k). The dk correction vanishes only after the exact full wedge because k=k(J,z). BOTH elliptic channels and the nonconstant 1/k source unit remain.',
 'WHOLE_reduced_target':'beta=(1/(72k))*dJ wedge(dU/Vplus+dU/Vminus) wedge dz wedge partial_H(dp/Y)|C, with Y^2=(H+Cp)^2−4p^6,H=J+3zC/2. This is the complete original reduced target, before any compact/PF projection.',
 'FULL_fixed_C_normal':{'E':str(E),'Nu':str(Nu),'Nw':str(Nw),'Nq':str(Nq),'Nk':str(Nk),'NJ':'1','Nz':'0','NC':'0','Nt':'−2t/B','N_one_over_k':'−2/(3B*k)'},
 'normal_scope':'The physical H-normal keeps(C,z) fixed and has NJ=1. It changes u,w,q,k,t and both elliptic points exactly; ordinary partial_J at fixed w would be wrong.',
 'actual_point':{'u':'1','w':'1','q':'1','J':'13/4','z':'1','E':str(ev(E)),'Nu':str(ev(Nu)),'Nw':str(ev(Nw)),'Nq':str(ev(Nq)),'B':str(ev(B))},
 'checks':checks,'check_count':len(checks),
 'credit':'The new source-preserving quotient w=y^2/x and literal pQ=−3z/2 source mark were derived here; fresh_algebraic_construction supplied the two standard elliptic quotient formulas, independently total-differentiated here.',
 'open':'Need an actual current/correspondence integrating both displayed source channels while retaining q^2=u*w, the full fixed-C normal, moving k/t terms, endpoint moduli and all canonical inverse-branch K factors if transported further. No primitive/certificate or CM claim.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'whole source, both actual elliptic channels, full normal and moving-source-unit checks')
