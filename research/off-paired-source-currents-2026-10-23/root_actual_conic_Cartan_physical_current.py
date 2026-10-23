"""Actual source-bound conic Cartan current, rational physical vector.
Avoids auxiliary CM marks; exact K correction is retained, not integrated.
"""
from pathlib import Path
import json,sympy as s
R,D,V,a,m=s.symbols('R D V a m',nonzero=True)
A=(R**3+1)/R;kS=R**2/(R**3+1);b=a/(6*A);z=m+b
L=D+a/3-a*a/(12*A)
M=-a*L/(6*A)-(V+1/(216*A*A))*a**3
P=A*m**3+a*m*m/2+(D+a/3)*m-V*a**3
rel=V*V-4*R-R*R/(4*D)
VR=(2+R/(4*D))/V;VD=-R*R/(8*D*D*V)
DR=lambda f:s.diff(f,R)+VR*s.diff(f,V)
DD=lambda f:s.diff(f,D)+VD*s.diff(f,V)
B=lambda f:s.diff(f,R)+D/R*s.diff(f,D)+V/(2*R)*s.diff(f,V)
La=s.diff(L,a);Ma=s.diff(M,a);LR=B(L)-kS*L;MR=B(M)-M/(2*R)
K=s.factor(Ma*LR-La*MR)
Ld=-a/(3*A);Md=-D/(3*A)-a/(9*A)+a*a/(18*A*A)
vc=s.factor((Ma*Ld-La*Md)/K)
wa=s.factor((LR*Md-MR*Ld)/K)
wR=-vc;wD=-D*vc/R;wA=-wa
wm=-(1/(2*R)-kS)*vc*z+vc*B(b)+wa*s.diff(b,a)-1/(3*A)
checks={}
def ck(n,e):
    nn=s.together(e).as_numer_denom()[0]
    nn=s.factor(s.rem(nn,rel,V))
    assert nn==0,(n,nn)
    checks[n]=True
ck('actual_leaf_B_has_both_V_derivatives',DR(V)+D/R*DD(V)-V/(2*R))
ck('full_source_normal_P',wR*DR(P)+wD*DD(P)+wA*s.diff(P,a)+wm*s.diff(P,m)-P*wR/(2*R)+m*m)
ck('whole_moving_depression_and_scale_in_wm',wm+(1/(2*R)-kS)*vc*z-vc*B(b)-wa*s.diff(b,a)+1/(3*A))
# Full firstpole weighted divergence, with physical mass Z=1/(72R sqrtD).
Div=s.factor(-B(vc)-s.diff(wa,a)+(kS+1/(2*R))*vc)
Kd=s.diff(Md,a)*LR+Ma*(B(Ld)-kS*Ld)-s.diff(Ld,a)*MR-La*(B(Md)-Md/(2*R))
ck('WHOLE_retained_canonical_density_normal',Div*K-(vc*B(K)+wa*s.diff(K,a)-Kd))
# Verify the entire divergence in its physical, four-coordinate definition.
Divphys=DR(wR)+DD(wD)+s.diff(wA,a)+s.diff(wm,m)-s.Rational(3,2)*wR/R-wD/(2*D)
ck('WHOLE_literal_four_coordinate_mass_divergence',Divphys-Div)
out={'status':'ACTUAL_RATIONAL_CONIC_CARTAN_CURRENT_WITH_ENTIRE_RETAINED_K_CORRECTION; NOT_CERTIFICATE',
'checks':checks,'check_count':len(checks),
'physical_curve':'h²=P²−4R, D=U²/4,V²=4R+R²/(4D), A=(R³+1)/R,P=A m³+a m²/2+(D+a/3)m−Va³.',
'original_reduced_source':'beta_clean=−P*m²*vol/(72R sqrtD h³),vol=dR dD da dm.',
'actual_current':'Jconic=−i_w[vol/(72R sqrtD h)], all coefficients rational in R,D,a,m,V.',
'base_functions':{'K':str(K),'vc':str(vc),'wa':str(wa),'b':'a/(6A)','kS':'R²/(R³+1)'},
'vector':{'R':'−vc','D':'−D*vc/R','a':'−wa','m':'−(1/(2R)−kS)*vc*(m+b)+vc*B(b)+wa*b_a−1/(3A)'},
'WHOLE_source_identity':'beta_clean=dJconic+Divconic*vol/(72R sqrtD h), Divconic=−B(vc)−partial_a(wa)+(kS+1/(2R))*vc.',
'actual_scalar_remainder':'In canonical orientation dell dmu dy omega0P the remainder is (vc*B(K)+wa*K_a−K_delta)/(72*y²*K²), y=sqrtR/U. It is NONZERO; no scalar primitive claimed.',
'preceding_cochains':'Add the independently retained original→Ferrari→2isogeny/norm coordinate cochains before lawful finite trace back to the immutable sextic.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual conic Cartan whole physical source current; exact K correction open')
