#!/usr/bin/env python3
"""Exact source-bound compact target checkpoint, without expanding K.

For R=(Z-1)K, [D,Z]=0 and Dv=6v give
Z[(D-7)K/v]=(D-7)R/v.  This evaluates that literal rational forcing using
the actual source and authoritative CRT arrays; it is not an exclusion.
"""
from __future__ import annotations

import importlib.util
import json
import time
from fractions import Fraction as Q
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location('fraction_jet',ROOT/'audit/ruling/verify_actual_lifts_fraction.py')
jetmod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(jetmod)
jetmod.ORDER=5
Jet=jetmod.Jet
evaluate=jetmod.evaluate
var=jetmod.variable


def evaluate_at_order(order):
    jetmod.ORDER=order
    started=time.monotonic()
    data=HERE.parent.parent/'genus4-gm-independent'
    potentials=json.loads((data/'cubic-residue-potentials-results.json').read_text())
    actual=potentials['actual_Ssrc_residue']
    # This is the actual R=S=z=k=1 physical point in rational coordinates.
    i,j,w=[var(x,n) for n,x in enumerate([Q(8,3),Q(1),Q(1)])]
    u=j/i**2
    env={'u':u}
    def array(name):
        return sum((evaluate(c,env)*w**n for n,c in enumerate(actual[name])),Jet())
    f=array('PE_residue_f_coefficients')
    g=array('PD_residue_g_coefficients')
    crt=array('CRT_factor_coefficients')
    T=1+w**3;N0=9*w**2-16*u*T
    L0=256*T**5*N0+729*i**6*u*w**6
    v=64*u*w*N0*T**2/(9*L0)
    vi,vj,vw=[v.partial(n) for n in range(3)]
    def A(x):return x.partial(0)-vi/vw*x.partial(2)
    def B(x):return x.partial(1)-vj/vw*x.partial(2)
    def Z(x):return v/vw*x.partial(2)
    def D(x):return 6*Z(x)-2*i*A(x)-2*j*B(x)
    def op(x,V,c=0):return V(x)+c*x
    h=v**2/vw*(54*w*T/(i*u*N0))
    F=v**2/vw*(f/i)*(18*w-48*u*w**2)/N0
    G=v**2/vw*g*(18*w-48*u*w**2)/N0
    t=i**-4*w*T*L0*crt
    H=v*t
    source=op(op(h,D,-5),D,-6)
    pe=op(op(F,D,-5),D,-6)+A(Z(F)+D(F)/2-2*F)
    pd=4*j*B(B(G))+2*B(G)+A(Z(G)+j*B(G))
    inner=Z(Z(H)+D(H)/2+H)
    p3=A(A(A(H)))+v*(Z(inner)+j*B(inner)+inner)
    # P3=A^3+v(Z+JB+1) Z (Z+D/2+1).
    remainder=source-pe-pd-p3
    forced=((D(remainder)-7*remainder)/v).value
    output={
        'source_sha256':potentials['source_sha256'],
        'point':{'i':'8/3','J':'1','w':'1','physical':'R=S=z=k=1'},
        'arithmetic':f'exact stdlib Fraction total-order-{order} jets, actual i/J/w coordinate derivatives',
        'identity':'Z[(D-7)K/v]=(D-7)[Ssrc-PEF-PDG-P3(vt)]/v',
        'actual_remainder_value':str(remainder.value),
        'forced_Z_derivative':str(forced),
        'nonzero':bool(forced),
        'scope':'Actual retained compact forcing checkpoint; no restriction or nonexistence claim. Full compact/infinity source remains.',
        'elapsed_seconds':time.monotonic()-started,
    }
    return output


def main():
    first=evaluate_at_order(5)
    second=evaluate_at_order(6)
    for name in ['actual_remainder_value','forced_Z_derivative']:
        assert first[name]==second[name],name
    second['arithmetic']='exact stdlib Fraction jets at total orders five and six, actual i/J/w coordinate derivatives'
    second['exact_values_match_orders']=[5,6]
    second['elapsed_seconds']+=first['elapsed_seconds']
    (HERE/'compact-target-checkpoint-results.json').write_text(json.dumps(second,indent=2)+'\n')
    print(json.dumps(second,indent=2))


if __name__=='__main__':main()
