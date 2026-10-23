"""Source-guided full-family tangent to the canonical-quadric qt coefficient."""
import sympy as s,json
from pathlib import Path
R,S,z=s.symbols('R S z',nonzero=True)
T=1+z**6;t=6*z**6/T
A=3-2*S+S/R;B=-2+6*S-4*S/R;K=8-12*S+4*S/R
Z=s.factor(K/(z*(A*t+B)));alpha=t*Z
v=s.factor(s.Rational(3,2)*(alpha-Z-2/z));u=s.factor(-Z-v/3)
VR=s.factor((1+R)*(alpha-2*u-2*v));VS=s.factor((1+S)*(alpha+2*u-2*v));Vz=s.factor(z*Z)
c=s.factor(-alpha-u+5*v/3)
div=s.diff(VR,R)+s.diff(VS,S)+s.diff(Vz,z)-s.Rational(5,6)*(VR/R+VS/S)
res=s.factor(div+c)
print('V_R',VR,flush=True);print('V_S',VS,flush=True);print('V_z',Vz,flush=True);print('residual',res,flush=True)
out={'variables':'R=r²,S=s²=k6/r²,mu∝R^(−5/6)S^(−5/6)dR dS dz','VR':str(VR),'VS':str(VS),'Vz':str(Vz),'torus_u':str(u),'torus_v':str(v),'alpha':str(s.factor(alpha)),'eta_b_scalar':str(c),'retained_residual':str(res),'certificate':res==0}
Path(__file__).with_name('canonical-qt-transport.json').write_text(json.dumps(out,indent=2)+'\n')
