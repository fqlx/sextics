import sympy as s
from pathlib import Path
import json
k,u=s.symbols('k tau');V=k*k-4;Q=k**3-3*k-u
R=(k**3-4*u)/V;L=k**3-12*k+8*u
assert s.cancel(s.diff(R,k)-k*L/V**2)==0
assert s.expand(L**2*Q-((k**3-4*u)**3-27*(k**3-4*u)*V**2+27*u*V**3))==0
# Z^2=slope^3*V*Q, Y=L*Z/V^2.
# Then Y^2=slope^3*(R^3-27R+27tau) and dR/Y=k*dk/Z.
out={'map_R':'(k^3-4*tau)/(k^2-4)','map_Y':'(k^3-12*k+8*tau)*Z/(k^2-4)^2','target':'Y^2=slope^3*(R^3-27*R+27*tau)','differential':'dR/Y=k*dk/Z','j':'6912/(4-tau^2)','status':'exact polynomial and differential identities checked; no global Hol2/Gysin assertion'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
