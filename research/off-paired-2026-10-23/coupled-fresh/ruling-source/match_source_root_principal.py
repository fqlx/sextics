"""Source-driven critical-fold match for a regular inverse-root moment.

At a fixed generic (i,J), the critical polynomial is exact and finite. This
computes the unique polynomial G_w modulo that polynomial which matches the
actual source's order-five fold pole under the cubic adjoint. It is a positive
local algebraic construction, not a certificate or a bounded exclusion.
"""
from pathlib import Path
import json
import sympy as s

I,J,v,w=s.symbols('I J v w')
T=1+w**3
N=9*I**2*w**2-16*J*T
M=256*T**5*N+729*I**6*J*w**6
P=9*I**2*v*M-64*J*w*T**2*N
PARAM_PARTS={n:s.diff(P,x) for n,x in [('i',I),('J',J),('v',v)]}

def run(i0=1,j0=1,prime=1009):
    subs={I:i0,J:j0}
    pp=s.Poly(P.subs(subs),v,w,modulus=prime)
    vn=s.Poly((64*J*w*T**2*N).subs(subs),w,modulus=prime)
    vd=s.Poly((9*I**2*M).subs(subs),w,modulus=prime)
    gd=s.gcd(vn,vd);vn=vn.exquo(gd);vd=vd.exquo(gd)
    critical=vn.diff()*vd-vn*vd.diff()
    # Remove fixed v=0 and v=infinity ramification; retain generic fold points.
    while True:
        gg=s.gcd(critical,vn*vd)
        if gg.degree()==0:break
        critical=critical.exquo(gg)
    critical=critical.sqf_part().monic()
    def mod(x):return s.Poly(x,w,modulus=prime).rem(critical)
    vp=(vn*s.invert(vd,critical)).rem(critical)
    def evalpart(expr):
        expr=s.Poly(expr.subs(subs),v)
        ans=mod(0)
        for (n,),coef in expr.terms():ans+=(mod(coef)*vp**n).rem(critical)
        return ans.rem(critical)
    pi,pj,pv=[evalpart(PARAM_PARTS[n]) for n in ('i','J','v')]
    kz=(vp*pv).rem(critical)
    kd=(6*kz-2*i0*pi-2*j0*pj).rem(critical)
    k1=(kz+j0*pj).rem(critical)
    k3=(4*kz-i0*pi-j0*pj).rem(critical)
    sigma=(pi**3+vp*k1*kz*k3).rem(critical)
    sigma1=(kd**2+pi*k3).rem(critical)
    sigma2=(4*j0*pj**2+pi*k1).rem(critical)
    nsrc=(-3456*i0**3*vp*mod(w*w*T**3)).rem(critical)
    target=(-nsrc*kd**2).rem(critical)
    gg=s.gcd(sigma,critical)
    if gg.degree():
        result={'status':'noninvertible cubic principal symbol','critical_degree':critical.degree(),
                'symbol_gcd_degree':gg.degree(),'target_mod_gcd':str(target.rem(gg).as_expr())}
    else:
        derivative=(target*s.invert(sigma,critical)).rem(critical)
        assert (sigma*derivative-target).rem(critical).is_zero
        coeff=[int(derivative.nth(j))%prime for j in range(critical.degree())]
        primitive=[0]+[x*pow(j+1,-1,prime)%prime for j,x in enumerate(coeff)]
        nfixed=mod(N.subs(subs))
        qfixed=s.Poly(N.subs(subs)**2,w,modulus=prime)
        crt_h=(derivative*s.invert(qfixed*critical.diff(),critical)).rem(critical)
        crt_moment=qfixed*critical*crt_h
        assert crt_moment.rem(qfixed).is_zero
        assert (crt_moment.diff()-derivative).rem(critical).is_zero
        result={'status':'actual order-five fold pole matched','critical_degree':critical.degree(),
                'symbol_gcd_degree':0,'regular_moment_degree':len(primitive)-1,
                'derivative_coefficients_ascending':coeff,
                'primitive_coefficients_ascending':primitive,
                'N_preserving_CRT_moment_degree':crt_moment.degree(),
                'N_preserving_CRT_coefficients_ascending':[int(crt_moment.nth(j))%prime for j in range(crt_moment.degree()+1)],
                'N_preserving_CRT_checks':['N² divides moment','moment derivative equals forced source derivative modulo critical polynomial'],
                'critical_polynomial_ascending':[int(critical.nth(j))%prime for j in range(critical.degree()+1)],
                'literal_remainder_check':True}
    result|={'prime':prime,'i':i0,'J':j0,
       'quadratic1_symbol_gcd_degree':s.gcd(sigma1,critical).degree(),
       'quadratic2_symbol_gcd_degree':s.gcd(sigma2,critical).degree(),
       'combined_quadratic_symbol_gcd_degree':s.gcd(s.gcd(sigma1,sigma2),critical).degree(),
       'meaning':'G_w sigma3 = −Nsrc KD² modulo(P,Pw), with v eliminated; only the leading source fold pole is matched',
       'remaining':'lift rational i,J coefficients, subtract full cubic adjoint, match order-three folds via quadratic rows, retain every remaining source/infinity term; no primitive claimed'}
    return result

if __name__=='__main__':
    out=[run(1,1),run(2,3),run(5,7)]
    Path(__file__).with_name('source-root-principal-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in d.items() if 'coefficients' not in k and 'polynomial' not in k} for d in out],indent=2))
