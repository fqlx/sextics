"""Forced first full-base current for the immutable source's compact form.

This constructs an actual source-carrying current and its exact remaining
rank-eight coefficient.  It does not assert that the remainder vanishes.
"""
import hashlib,json,time
from pathlib import Path
import sympy as s
from flint import fmpq_mpoly_ctx,fmpq_mpoly

HERE=Path(__file__).resolve().parent
T=fmpq_mpoly_ctx.get(('i','j','v'))
i,j,v=T.gens();zero=T.constant(0)

def main():
    started=time.monotonic()
    srcij=HERE/'rank8-ij-connections-results.json'
    srcv=HERE/'rank8-v-literal-primitives-results.json'
    ij=json.loads(srcij.read_text());vv=json.loads(srcv.read_text())
    assert ij['primitive_words']==vv['primitive_words']
    Di=fmpq_mpoly(ij['common_denominator'],T)
    Dv=fmpq_mpoly(vv['common_denominator'],T)
    den=Di*(Dv//Di.gcd(Dv))
    fi=den//Di;fv=den//Dv
    # b is the seventh compact basis vector.  Use the literal exact
    # primitives, including the V Cartan correction, in the same column.
    col=6
    Ri=[]
    for row in range(8):
        Gi=fmpq_mpoly(ij['Gamma_numerators']['i'][row][col],T)
        Gj=fmpq_mpoly(ij['Gamma_numerators']['j'][row][col],T)
        GV=fmpq_mpoly(vv['GammaV_numerators'][row][col],T)
        Ri.append((4*den if row==col else zero)-fv*GV+2*i*fi*Gi+j*fi*Gj)
    FD=[]
    for row in range(16):
        pi=fmpq_mpoly(ij['primitive_numerators']['i'][row][col],T)
        pj=fmpq_mpoly(ij['primitive_numerators']['j'][row][col],T)
        pv=fmpq_mpoly(vv['primitive_numerators'][row][col],T)
        FD.append(fv*pv-2*i*fi*pi-j*fi*pj)
    common=den
    for z in Ri+FD:
        common=common.gcd(z)
        if common==1:break
    den=den//common;Ri=[z//common for z in Ri];FD=[z//common for z in FD]

    # This arbitrary-function check fixes the flat-volume divergence and
    # the constant four in the exact residual, not a trial coefficient.
    xx,yy,zz=s.symbols('i j v',nonzero=True)
    h=s.Function('h')(xx,yy,zz)
    DD=lambda f:6*zz*s.diff(f,zz)-2*xx*s.diff(f,xx)-yy*s.diff(f,yy)
    TT=h/(6*zz**2)
    divergence=s.diff(-2*xx*TT,xx)+s.diff(-yy*TT,yy)+s.diff(6*zz*TT,zz)
    assert s.simplify((DD(h)-5*h)/(6*zz**2)-divergence-4*TT)==0

    out={
        'status':'Actual first full-base current and exact compact remainder; closure open',
        'volume':'mu=di wedge dj wedge dv; relative curve form first',
        'source_origin':'Original normalized source -Hsrc*partial_e^2(zeta), Hsrc=e^-5*hsrc. One source integration by parts gives +(D-5)hsrc/(6v^2)*nu_b in this flat volume.',
        'source_vector':'S=(D-5)hsrc/(6*v^2)*e_b, e_b=index6, D=6v*partial_v-2i*partial_i-j*partial_j',
        'actual_branch':['T=1+w^3','N=9*i^2*w^2-16*j^2*T','M=256*T^5*N+729*i^6*j^2*w^6','v=64*j^2*w*T^2*N/(9*i^2*M)'],
        'source_density_identity':'hsrc*v_w/v^2=54*i^3*w*T/(j^2*N)',
        'current_coefficients':'P_i=-2i*t*e_b, P_j=-j*t*e_b, P_v=6v*t*e_b, t=hsrc/(6v^2)',
        'current_convention':'Jbase=-sum_p (nu dot P_p) wedge contraction_partial_p(mu); Jfiber=-sum_p (fiberprimitive_p dot P_p)*mu',
        'remaining_native':'R=t*(4*e_b-GammaD*e_b), GammaD=GammaV-2i*Gamma_i-j*Gamma_j',
        'remaining_physical':'R_w=9*i^3*w*T/(j^2*N)*(4*e_b-GammaD*e_b), volume di wedge dj wedge dw',
        'remaining_common_denominator':str(den),
        'remaining_vector_numerators':[str(z)for z in Ri],
        'fiber_primitive_D':'fD_b=(sum primitive_D_numerator[word]*word)/(remaining_common_denominator*Jbar)',
        'fiber_primitive_words':ij['primitive_words'],
        'fiber_primitive_D_numerators':[str(z)for z in FD],
        'fiber_current':'-t*fD_b*mu',
        'connection_inputs_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in (srcij,srcv)},
        'checks':{'full_euler_divergence_for_arbitrary_h':True,'all_three_base_directions_used':True,'literal_primitive_D_including_V_Cartan_retained':True,'no_inverse_map_critical_denominator_in_remaining_physical_density':True},
        'certificate':False,'seconds':round(time.monotonic()-started,3)}
    path=HERE/'source-euler-current-results.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print('actual source Euler current+exact8vector remainder saved',out['seconds'],flush=True)
    print('remaining denominator degree',den.degrees(),'terms',len(den.to_dict()),flush=True)

if __name__=='__main__':main()
