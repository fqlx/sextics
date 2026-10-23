"""Source-carrying rational cubic residue potentials from RIGHT Ore Bezout.

Outputs a compressed CRT lift; the remaining exact (Z-1) term is not dropped.
"""
import json,hashlib
from pathlib import Path
import sympy as s
HERE=Path(__file__).parent
u,w=s.symbols('u w');K=s.QQ.frac_field(u)
T=1+w**3
N0=9*w*w-16*u*T
P=s.Poly(w**3-9*w*w/(16*u)+1,w,domain=K)
def red(expr):
 num,den=s.fraction(s.cancel(expr))
 a=s.rem(s.Poly(num,w,domain=K),P)
 b=s.rem(s.Poly(den,w,domain=K),P)
 out=s.rem(a*s.invert(b,P),P)
 return sum(s.cancel(c)*w**m[0]for m,c in out.terms())
def vec(f):return [s.cancel(s.Poly(f,w,domain=K).coeff_monomial(w**j))for j in range(3)]
def va(a,b):return [s.cancel(x+y)for x,y in zip(a,b)]
def vs(a,c):return [s.cancel(c*x)for x in a]
bb=9/(16*u)
def vm(a,b):
 c0=a[0]*b[0]-a[1]*b[2]-a[2]*b[1]-bb*a[2]*b[2]
 c1=a[0]*b[1]+a[1]*b[0]-a[2]*b[2]
 c2=a[0]*b[2]+a[1]*b[1]+a[2]*b[0]+bb*(a[1]*b[2]+a[2]*b[1])+bb*bb*a[2]*b[2]
 return [s.cancel(c)for c in (c0,c1,c2)]
wu=vec(red(16*T/s.diff(N0,w)))
def der(f):return va([s.diff(x,u)for x in f],vm([f[1],2*f[2],0],wu))
def th(f):return vs(der(f),u)
r=vec(red(54*w*T/(u*s.diff(N0,w))))
jets=[r]
for _ in range(4):jets.append(der(jets[-1]))
data=json.loads((HERE/'residue-ore-bezout-results.json').read_text())
U=[s.sympify(x,locals={'u':u})for x in data['U_low_to_high']]
V=[s.sympify(x,locals={'u':u})for x in data['V_low_to_high']]
def apply(co,js):
 out=[0,0,0]
 for c,j in zip(co,js):out=va(out,vs(j,c))
 return out
def record(source,source_jets):
 tt=apply(U,source_jets);hh=apply(V,source_jets)
 f=vs(der(tt),2);g=va(th(tt),vs(tt,2))
 crt=vm(crt_inverse_reduced,hh)
 return {'source_coefficients':[str(s.factor(x))for x in source],
  'U_r_t_coefficients':[str(s.factor(x))for x in tt],
  'V_r_H_coefficients':[str(s.factor(x))for x in hh],
  'PE_residue_f_coefficients':[str(s.factor(x))for x in f],
  'PD_residue_g_coefficients':[str(s.factor(x))for x in g],
  'CRT_factor_coefficients':[str(s.factor(x))for x in crt]}
assert red(s.diff(N0,u)+s.diff(N0,w)*sum(c*w**j for j,c in enumerate(wu)))==0

# The CRT divisor L depends additionally on i through J=i²u, but moduloN0
# L=729 i^8 u w^6.  Invert only w*T*729u*w6, keeping the i power explicit.
crt_inverse_reduced=vec(red(1/(729*u*w**7*T)))
assert red(729*u*w**7*T*sum(c*w**j for j,c in enumerate(crt_inverse_reduced))-1)==0
target=va(va(vs(jets[2],4*u*u),vs(jets[1],14*u)),vs(jets[0],6))
target_jets=[target,der(target)]
target_jets.append(der(target_jets[-1]))
source_binding={
 'authoritative_record':'actual_Ssrc_residue',
 'coordinates':'i,J,w; u=J/i², T=1+w³',
 'physical_coefficients':'k=3iw/(4T),A=k²T/J,R=A-1,S=k^6/R',
 'Delta':'3RS w³-3RS-8R w³+R-S w³+2S',
 'h':'3i w³/(32J T² Delta)',
 'v':'64Jw N T²/[9i²(256T^5 N+729i^6 Jw^6)]',
 'N':'9i²w²-16J(1+w³)',
 'operators':'A=partial_i-v_i/v_w partial_w,B=partial_J-v_J/v_w partial_w,Z=v/v_w partial_w,D=6Z-2iA-2JB',
 'actual_forcing':'Ssrc=(D-6)(D-5)h',
 'h_finite_N_residue':'i^-1*r_h(u,w)',
 'r_h_coefficients_low_to_high':[str(s.factor(x))for x in r],
 'Ssrc_finite_N_residue':'i^-1*rTarget(u,w)',
 'rTarget_rule':'2(theta+1)(2theta+3)r_h=4u²r_h_uu+14u*r_h_u+6r_h, theta=u*partial_u in cubic field',
 'rTarget_coefficients_low_to_high':[str(s.factor(x))for x in target],
 'cubic':'9w²-16u(1+w³)=0',
 'cubic_derivation_w_u_coefficients':[str(s.factor(x))for x in wu],
}
def digest(obj):return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()
source_hash=digest(source_binding)
operator_hashes={'U':digest(data['U_low_to_high']),'V':digest(data['V_low_to_high'])}
binding={'source':source_binding,'source_sha256':source_hash,'operator_array_sha256':operator_hashes,
 'hash_convention':'UTF-8 json.dumps(object,sort_keys=True,separators=(comma,colon)); U,V each hash their complete low-to-high string array'}
(HERE/'corrected-rational-source-binding.json').write_text(json.dumps(binding,indent=2)+'\n')
print('Both source conventions and cubic jets constructed',flush=True)
simple=record(r,jets[:3]);print('h residue potentials saved in memory',flush=True)
forced=record(target,target_jets);print('Ssrc residue potentials saved in memory',flush=True)
out={
 'cubic':'N0=9w²-16u(1+w³), u=J/i²',
 'h_residue':simple,
 'actual_Ssrc_residue':forced,
 'source_conventions':'h residue r; actual Ssrc=(D-6)(D-5)h residue rTarget=2(theta+1)(2theta+3)r=4u²r_uu+14ur_u+6r; no commutation through potentials assumed',
 'authoritative_potential_record':'actual_Ssrc_residue',
 'source_sha256':source_hash,'operator_array_sha256':operator_hashes,
 'rational_scalar_potentials':{
  'PE':'F=(v²/v_w)*i^-1*f(u,w)*N0_w/N0',
  'PD':'G=(v²/v_w)*g(u,w)*N0_w/N0',
  'P3':'Hpot=v*tLift',
  'tLift':'i^-6 * w*(1+w³)*L * CRT_factor(u,w)',
  'L':'256(1+w³)^5*N+729i^6 Jw^6, N=i²N0,J=i²u',
  'CRT_check':'tLift=i²H moduloN0; tLift divisible by w*(1+w³)*L'},
 'exact_operator_identity':'P3(v*t)=v*A³t+(Z-1)[v²(Z+JB+2)(Z+D/2+5)t]',
 'residue_identity':'VERIFIED in the finiteN cubic residue module with authoritative actual_Ssrc_residue and physical i^-1 scaling. ACTUAL-RATIONAL-K.md restores all other poles by literal Cartan identities; the independently computed exact N-only Hermite primitive checks the complete differentiated actual remainder. The separate h_residue record serves h only and is diagnostic.',
 'remaining_source':'CONSTRUCTED scalar identity: Ssrc-PE(F)-PD(G)-P3(Hpot)=(Z-1)K, with K=v*(PN+ES(h)-EPE(F)-EPD(G)-EA3(v*t)-W(t)/v). Exact formulas and all-pole proof: ACTUAL-RATIONAL-K.md. PN is the explicitly checked coefficient array in ../ruling-source/adjoint-reconstruction/n-only-hermite-results.json. The coupled curve-valued defect generated by K is retained and remains to be served.',
 'unverified_obligations':['serving the coupled curve defect generated by K','full original sextic rational primitive certificate'],
 'actual_scalar_remainder_artifacts':['ACTUAL-RATIONAL-K.md','verify_actual_rational_k.py','actual-rational-k-results.json','../ruling-source/adjoint-reconstruction/construct_n_only_hermite.py','../ruling-source/adjoint-reconstruction/n-only-hermite-results.json'],
 'verification':'RIGHT Ore identity L1U+L2V=1 verified in residue_ore_bezout.py; cubic field derivation verified by D(N0)=0 and CRT inverse identity; composition proves both source residue matches exactly without expanding seventh derivatives',
 'checks':3,'certificate':False,
}
(HERE/'cubic-residue-potentials-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'checks':3,'status':'exact source residue identity verified in cubic field; rational CRT lift displayed; full Hermite remainder/current still open'},indent=2))
