#!/usr/bin/env python3
"""Exact finite first-elliptic factor and parameter derivative split."""
import sympy as s
S,T=s.symbols('S T')
P=S*T
D=S**3-T**3
H=S**3+T**3
K=S*S+S*T+T*T
q=-(S+T)/(2*K)
def de(f):
    return 3*T*T*s.diff(f,S)-3*S*S*s.diff(f,T)
def zero(x):
    assert s.cancel(x)==0
N=-3*S*T*(S*S-T*T)/K**2
zero(de(P)+3*D)
zero(de(D)-18*P**2)
zero(D**2-H**2+4*P**3)
zero(de(q)-N)
zero(de(N)-36*P*q+3*(H**2+8*P**3)*N/(P*D))

A=q*D/P**2
zero(de(A)-D*N/P**2-6*(H**2/P**3-1)*q)
zero(de(P**3)+9*P**2*D)

# For g=A*g0(d), d=P^3, the actual first-E parameter derivative is
# A' g0+A d' g0_d; neither term may be omitted on the diagonal.
g0,g0d=s.symbols('g0 g0d')
split=D*N*g0/P**2+6*(H**2/P**3-1)*q*g0-9*D**2*q*g0d
zero(de(A)*g0+A*de(P**3)*g0d-split)
print('PASS: eight exact first-elliptic module and parameter-jet identities.')
