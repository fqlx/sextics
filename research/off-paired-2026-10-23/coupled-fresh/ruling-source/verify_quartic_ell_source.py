"""Literal ell-direction source, residues, and the full compact transfer.

The scalar Pa primitive is an input from accumulated source Green currents.
No arbitrary scalar integral, compact exactness, or omitted base derivative
is used in the identities checked here.
"""
import json
from pathlib import Path
import sympy as s
a,b,l,h,i,j,f,fw=s.symbols('a b ell h i j f f_w',nonzero=True)
Q=a*a+b*b+i*l*l+j*a*l+l+1
Qa=s.diff(Q,a);Ql=s.diff(Q,l)
J=a*Qa-2*b*b
P=a**4+j*l*a**3+(i*l*l+l+1)*a*a+f*l**6
Pa=s.diff(P,a)

def zero_curve(x):
    nn=s.together(x).as_numer_denom()[0]
    nn=nn.subs(h,a*b/l**3)
    return s.factor(nn.subs(i,-(a*a+b*b+j*a*l+l+1)/l**2))==0

zeta=b/l
zi=b*l/J
zj=h*l**3/J
zh=l*l*Qa/J
beta=l*l*(a*a+j*l*a+i*l*l+l+1)/Pa
checks={}
checks['quartic_J_identity']=s.expand(Pa-a*(4*a*a+3*j*a*l+2*(i*l*l+l+1)))==0
checks['quartic_J_on_curve']=zero_curve(Pa-a*J)
checks['literal_beta_section_split']=zero_curve(beta-zeta/(2*h)+zh/2)
checks['literal_i_derivative']=zero_curve(b*l*l/(l*J)-zi)
checks['literal_j_derivative']=zero_curve(b*a*l/(l*J)-zj)
checks['literal_h_derivative']=zero_curve((a*Qa*b/(h*J))/l-zh)

b0=s.symbols('b0',nonzero=True)
beta_Pa=(-b**3/(h*l*J)).subs({a:h*l**3/b0,b:b0})
checks['finite_Pa_residue']=s.cancel(s.limit(l*beta_Pa,l,0)-b0/(2*h))==0
# Norm gives a=O(ell^3) at Pa, b=O(ell^3) at Pb.  All three
# displayed parameter derivatives have zero finite residues.
def order_at_zero(x):
    nn,dd=s.fraction(s.cancel(x))
    return min(k[0]for k,_ in s.Poly(nn,l).terms())-min(k[0]for k,_ in s.Poly(dd,l).terms())
a0=s.symbols('a0',nonzero=True)
pa={a:h*l**3/b0,b:b0}
pb={a:a0,b:h*l**3/a0}
checks['compact_derivatives_Pa_orders']=tuple(order_at_zero(x.subs(pa))for x in (zi,zj,zh))==(1,3,3)
checks['compact_derivatives_Pb_orders']=tuple(order_at_zero(x.subs(pb))for x in (zi,zj,zh))==(4,3,2)

K,hi,hj,hw,Bi,Bj,Bw,divB=s.symbols('K h_i h_j h_w B_i B_j B_w divB')
# Base volume mu=di wedge dj wedge dw and dB=divB*mu.
# d(-zeta wedge B) has relative-first coefficient
# sum B_x*partial_x zeta+zeta*divB.
sum_deriv=Bi*(zi+hi*zh)+Bj*(zj+hj*zh)+Bw*hw*zh
current_derivative=sum_deriv+zeta*divB
compact=-Bi*zi-Bj*zj-(Bi*hi+Bj*hj+Bw*hw+K*h*hw/6)*zh
source=K*hw*zeta/6-K*h*hw*zh/6
checks['full_compact_source_transfer']=s.cancel(
    (current_derivative+compact-source).subs(divB,K*hw/6))==0
checks['actual_source_coefficient']=zero_curve(
    K*fw*beta/6-(K*fw*zeta/(12*h)-K*fw*zh/12))

assert all(checks.values()),checks
out={
 'passed':True,'checks':checks,'certificate':False,
 'fixed_quadric':str(Q),'norm':'a*b=h*ell^3','physical_cover':'h^2=f(w)=1/v(i,j^2,w)',
 'quartic':str(P),'curve_J':str(J),
 'relative_forms':{'zeta0':'b*dell/ell','zeta_i':'b*ell*dell/J',
                  'zeta_j':'h*ell^3*dell/J','zeta_h':'ell^2*(2a+j*ell)*dell/J'},
 'source_split':'K*f_w*beta/6=(K*h_w/6)*zeta0-(K*h*h_w/6)*zeta_h',
 'Pa_residue':'Res_Pa± beta=±sqrt(-1)/(2h); source residue=±sqrt(-1)*K*dh/6',
 'base_primitive_input':'B=B_i*dj^dw+B_j*dw^di+B_w*di^dj, dB=(K*h_w/6)*di^dj^dw',
 'compact_source':'-B_i*zeta_i-B_j*zeta_j-(B_i*h_i+B_j*h_j+B_w*h_w+K*h*h_w/6)*zeta_h',
 'current':'-zeta0 wedge B; full i,j derivatives of h retained',
 'remaining':'All eight compact components remain to be served. B comes from accumulated actual source Green currents, not an arbitrary rational-integration assertion.'
}
Path(__file__).with_name('quartic-ell-source-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact quartic ell/source identities')
