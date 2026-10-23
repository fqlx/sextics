#!/usr/bin/env python3
"""Rational rank-ten compact+two-residue connection for the actual source.

All coefficient matrices use columns for differentiated basis forms.
A rational P with P_w+Gamma_w P=forcing constructs a source-carrying current.
"""
import json,time
from pathlib import Path
import sympy as s

c,d,e=s.symbols('c d e');i,j,v,w=s.symbols('i j v w')
weights=[1,2,3,4,5,1,2,4,5]

def descend(poly,shift):
    result=s.S.Zero
    for (C,D,E),coef in s.Poly(poly,c,d,e).terms():
        n=2*C+D+E+shift
        assert n%6==0,(C,D,E,shift,n)
        result+=coef*i**C*j**D*v**(n//6)
    return s.expand(result)

def main():
    path=Path(__file__).with_name('affine-V-generic-results.json')
    data=json.loads(path.read_text());den=s.sympify(data['common_denominator'])
    rden=next(iter(s.Poly(den,c,d,e).monoms()));rden=(2*rden[0]+rden[1]+rden[2])%6
    D=descend(den,-rden)
    G=s.Matrix(9,9,lambda rr,cc:descend(s.sympify(data['gamma_numerators'][rr][cc]),weights[cc]-weights[rr]-rden))
    G+=s.diag(*weights)*D
    Cp0=i-j*j/4;r0=Cp0*(Cp0-j*j)/8
    # Raw basis [1,q,q²,q³,q⁴,a,aq,b,bq]dq/J, each deck-gauged.
    # Compact basis [1,q,q³,q⁴-rq²,a,aq+dq²/2,b,bq], then omega.
    T=s.zeros(9,9)
    for cc,rr in enumerate([0,1,3,4,5,6,7,8,2]):T[rr,cc]=1
    T[2,3]=-v*r0;T[2,5]=j/2
    Ti=T.inv()
    Gc=(Ti*(G*T+6*v*D*T.diff(v))).applyfunc(s.expand)
    # The exact full generic connection must preserve the residue quotient.
    assert all(x==0 for x in Gc[8,:8])
    assert s.expand(Gc[8,8]-3*D)==0
    Full=s.zeros(10,10);Full[:9,:9]=Gc
    # V zeta=d q³/J+e b/J+2c bq/J; deck gauge contributes 3 zeta.
    Full[2,9]=j*D;Full[6,9]=D;Full[7,9]=2*i*D;Full[9,9]=3*D
    B=s.Matrix([
      -i*j*(12*i-j*j)*v/840,
      -i*j*(12*i-j*j)*v/840,
      -2*j/21,
      -j*(44*i-7*j*j)/280,
      i*(12*i-j*j)*v/420,
      (i*(96*i*i-44*i*j*j+3*j**4)*v-2880)/1680,
      -(456*i-3*j*j-80)/420,
      -(208*i-9*j*j)/840,
    ])
    kappa=j*(v*Cp0**3+8)/16
    forcing=list(-B)+[kappa,s.Rational(1,2)]
    p=Path(__file__).with_name('rank10-descended-connection-results.json')
    result={
      'status':'Exact generic rank10 source-carrying ODE interface; rational primitive still required',
      'coordinates':'i=c/e²,j=d/e,v=e⁶; actual v=v(w) is retained',
      'descended_curve':'a*y=x³; y²+v*(a²+i*x²+j*a*x+x+1)=0',
      'compact_basis':['1','q','q³','q⁴-Cp*(Cp-d²)*q²/8','a','a*q+d*q²/2','b','b*q'],
      'basis_convention':'nu_j=e^m_j*N_j*dq/J for m=[1,2,4,5,1,2,4,5], followed by omega_hat=e³*q²*dq/J and zeta_hat=e³*b*dq/q',
      'basis_weights':[1,2,4,5,1,2,4,5,3,3],
      'matrix_convention':'partial_w basis_j=sum_i Gamma_w[i,j]*basis_i+d_q(exact_primitive_j)',
      'Gamma_w':'v_w/(6*v)*GammaV_numerator/GammaV_denominator',
      'GammaV_denominator':str(s.factor(D)),
      'GammaV_numerator':[[str(s.factor(x)) for x in Full.row(r)] for r in range(10)],
      'omega_infinity_row':'GammaV row8 is [0,...,0,3,0]',
      'zeta_finite_row':'GammaV row9 is [0,...,0,0,3]',
      'omega_theta_compact_vector':[str(s.factor(x)) for x in B],
      'source_forcing_vector':[str(s.factor(x)) for x in forcing],
      'source_scalar':'v_w*(Dop-7)*Kreg/(12*j*v²)',
      'source_equation':'P_w+Gamma_w*P=source_scalar*source_forcing_vector',
      'Dop':'6Z-2i*A-j*partial_j_at_v; Z=v/v_w*partial_w, A=partial_i_at_w-v_i/v_w*partial_w, partial_j_at_v=partial_j_at_w-v_j/v_w*partial_w',
      'kernel_freedom':'Kreg can be replaced by Kreg+v*C(i,j)',
      'checks':{'generic_finite_affine_reduction_333_identities':data['all_333_generic_cleared_polynomial_identities'],'no_compact_to_residue_leakage':True,'both_residue_diagonals':True},
    }
    p.write_text(json.dumps(result,indent=2)+'\n')
    print('saved',p,flush=True)
    print('denominator',s.factor(D),flush=True)
if __name__=='__main__':main()
