#!/usr/bin/env python3
"""Exact finite reduction identities for the actual moving-sextic source jets.

No companion primitive or certificate is asserted. The inverses in the
mathematical construction exist generically since each operator is identity
at lambda=0; generating a large rational connection is unnecessary here.
"""
import json
import sympy as s
Y=s.symbols('Y0:3')
lam,b01,b12,b02,auxd,auxe=s.symbols('lam b01 b12 b02 auxd auxe')
C=sum(y**6 for y in Y)
B=b01*Y[0]*Y[1]+b12*Y[1]*Y[2]+b02*Y[0]*Y[2]
G=C+lam*B**3
Gi=[s.diff(G,y) for y in Y]
Bi=[s.diff(B,y) for y in Y]

def mons(degree):
    return [Y[0]**a*Y[1]**b*Y[2]**(degree-a-b)
            for a in range(degree+1) for b in range(degree-a+1)]

def fdiv(P):
    """P=normal+sum(A_i Y_i^5), choosing first available index."""
    normal=0
    A=[0,0,0]
    for exp,coeff in s.Poly(s.expand(P),*Y).terms():
        bad=next((i for i in range(3) if exp[i]>=5),None)
        if bad is None:
            normal+=coeff*s.prod(Y[i]**exp[i] for i in range(3))
        else:
            ee=list(exp)
            ee[bad]-=5
            A[bad]+=coeff*s.prod(Y[i]**ee[i] for i in range(3))
    return normal,A

def M(P):
    normal,A=fdiv(P)
    return s.expand(P+lam*B**2*sum(A[i]*Bi[i] for i in range(3))/2)

checks={}
for degree in (9,15):
    basis=mons(degree)
    ident=True
    identity_at_zero=True
    for mon in basis:
        normal,A=fdiv(mon)
        ident &= s.expand(M(mon)-normal-sum(A[i]*Gi[i] for i in range(3))/6)==0
        identity_at_zero &= s.expand(M(mon).subs(lam,0)-mon)==0
    checks[f'degree_{degree}_all_column_identities']=bool(ident)
    checks[f'degree_{degree}_identity_specialization']=bool(identity_at_zero)
    checks[f'degree_{degree}_dimension']=len(basis)=={9:55,15:136}[degree]
checks['degree_15_has_no_normal_terms']=all(fdiv(m)[0]==0 for m in mons(15))
checks['degree_9_normal_basis_has_ten_terms']=sum(fdiv(m)[0]!=0 for m in mons(9))==10
checks['degree_3_holomorphic_basis_has_ten_terms']=len(mons(3))==10

P=Y[0]**3*(C-2*lam*B**3)
gamma=P/G**2
checks['actual_lambda_jet']=s.factor(s.diff(gamma,lam)-(
    -4*Y[0]**3*B**3/G**2+6*lam*Y[0]**3*B**6/G**3))==0
for bb,qq in ((b01,Y[0]*Y[1]),(b12,Y[1]*Y[2]),(b02,Y[0]*Y[2])):
    checks[f'actual_{bb}_jet']=s.factor(s.diff(gamma,bb)-(
        -12*lam*Y[0]**3*B**2*qq/G**2+18*lam**2*Y[0]**3*B**5*qq/G**3))==0
J=G-auxd**3-auxe**3
checks['boundary_Euler_defect']=s.expand(sum(Y[i]*s.diff(J,Y[i]) for i in range(3))-6*J-6*(auxd**3+auxe**3))==0
checks['full_weighted_Euler']=s.expand(sum(Y[i]*s.diff(J,Y[i]) for i in range(3))+2*auxd*s.diff(J,auxd)+2*auxe*s.diff(J,auxe)-6*J)==0
checks['boundary_defect_double_log_residue_zero']=(
    s.expand(auxd**3+auxe**3).coeff(auxd,0).coeff(auxe,0)==0)
assert all(checks.values()), checks
print(json.dumps({'all_passed':True,'checks':checks,
 'column_identities_checked':191,
 'source_targets':['Y0^3 B^6','Y0^3 B^5 Y0Y1','Y0^3 B^5 Y1Y2','Y0^3 B^5 Y0Y2'],
 'claim':'Finite compatible source-jet reduction; no scalar primitive asserted.'},indent=2))
