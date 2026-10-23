"""Bounded actual-source rational-current screen in the quartic algebra.

u_i=P_i(z,base)/G_z.  Modulo G, clear G_z^3 in sum D_i u_i=rho.
Finite-field samples are a screen only; a positive result still needs an
exact rational-function identity.  A negative modular matrix is only a
statement about this polynomial numerator ansatz after good reduction.
"""
from pathlib import Path
from itertools import product
import json
import pickle
import random
import sys
import time
import os
import sympy as s
from flint import nmod_poly, nmod_mat

HERE = Path(__file__).parent
kind = os.environ.get("EIGHT_MODEL", "quartic")
modelname = "cubic_model.pickle" if kind == "cubic" else "model.pickle"
model = pickle.loads((HERE.parent/"eight_plane_quartic"/modelname).read_bytes())
names = ("a", "b", "c", "d") if kind == "cubic" else ("u1", "u2", "v1", "v2")
bs = [model["symbols"][x] for x in names]
fiber_degree = len(model["coefficients"])-1
source_coefficients = [0,0,1] if kind == "cubic" else [-1,0,3,0,-3,0,1]
prime = 1000003
def scalar(c):
    a,b = map(int, s.fraction(c))
    return a%prime*pow(b%prime,-1,prime)%prime
coefficients = [dict((m,scalar(c)) for m,c in s.Poly(f,*bs).terms())
                for f in model["coefficients"]]
def monomials(d):
    return sorted([e for e in product(range(d+1),repeat=4) if sum(e)<=d],
                  key=lambda e:(sum(e),e))
def evaluate(point):
    powers = [[pow(x,j,prime) for j in range(7)] for x in point]
    gs, derivatives = [], [[] for _ in range(4)]
    for f in coefficients:
        value = 0
        dv = [0]*4
        for e,c in f.items():
            term=c
            for j in range(4):
                term=term*powers[j][e[j]]%prime
            value=(value+term)%prime
            for j in range(4):
                if not e[j]:
                    continue
                t=c*e[j]
                for k in range(4):
                    t=t*powers[k][e[k]-(j==k)]%prime
                dv[j]=(dv[j]+t)%prime
        gs.append(value)
        for j in range(4):
            derivatives[j].append(dv[j])
    G=nmod_poly(gs,prime)
    if G.degree()!=fiber_degree:
        return None
    gp=G.derivative()
    if G.gcd(gp).degree()!=0:
        return None
    gpp=gp.derivative()
    zz=nmod_poly([0,1],prime)
    zp=[zz**j for j in range(fiber_degree)]
    vec=lambda poly:[int(poly[j]) for j in range(fiber_degree)]
    D=[vec((gp*gp*x)%G) for x in zp]
    C=[]
    for i in range(4):
        gi=nmod_poly(derivatives[i],prime)
        gpi=gi.derivative()
        row=[]
        for j in range(fiber_degree):
            term=(-gp*gpi+gi*gpp)*zp[j]
            if j:
                term-=j*gp*gi*zp[j-1]
            row.append(vec(term%G))
        C.append(row)
    N=nmod_poly(source_coefficients,prime)
    rhs=vec((N.derivative()*gp-N*gpp)%G)
    return C,D,rhs,dict(g=gs,derivatives=derivatives)

def point_block(point, data, mons):
    C,D,rhs=data[:3]
    d=max(map(sum,mons))
    powers=[[pow(x,j,prime) for j in range(d+1)] for x in point]
    rows=[[] for _ in range(fiber_degree)]
    for i in range(4):
        for e in mons:
            val=1
            for k in range(4):
                val=val*powers[k][e[k]]%prime
            derivative=0
            if e[i]:
                derivative=e[i]
                for k in range(4):
                    derivative=derivative*powers[k][e[k]-(i==k)]%prime
            for j in range(fiber_degree):
                for r in range(fiber_degree):
                    rows[r].append((val*C[i][j][r]+derivative*D[j][r])%prime)
    return [r+[rhs[k]] for k,r in enumerate(rows)]

def run(degree):
    start=time.monotonic()
    mons=monomials(degree)
    columns=4*fiber_degree*len(mons)
    # The tracezero sector has only n-1 effective equations per point.  A
    # trace constraint can have much lower function-space rank than the full
    # rank-n row count suggests, so oversample against n-1, not n.
    need=columns//(fiber_degree-1)+24
    rng=random.Random(910270+degree)
    rows=[];points=[]
    while len(points)<need:
        point=tuple(rng.randrange(1,prime) for _ in range(4))
        data=evaluate(point)
        if data is None:
            continue
        rows.extend(point_block(point,data,mons));points.append(point)
    mat=nmod_mat(rows,prime)
    rr,rank=mat.rref()
    coefficient_rank=sum(any(int(rr[i,j]) for j in range(columns)) for i in range(rank))
    consistent=(rank==coefficient_rank)
    ans=dict(prime=prime,model=kind,degree=degree,z_degree=fiber_degree-1,denominator="G_z",
             rows=len(rows),columns=columns,rank=coefficient_rank,
             augmented_rank=rank,consistent=consistent,
             seconds=time.monotonic()-start,
             scope="Finite-field sampled screen of the stated ansatz only; no generic or unrestricted conclusion.")
    prefix="cubic_" if kind=="cubic" else ""
    (HERE/f"{prefix}current_degree{degree}.json").write_text(json.dumps(ans,indent=2)+"\n")
    if consistent:
        # A candidate can be extracted by setting all free variables to zero.
        solution=[0]*columns
        for i in range(rank):
            pivot=next(j for j in range(columns) if int(rr[i,j]))
            solution[pivot]=int(rr[i,columns])
        valid=True
        for _ in range(100):
            point=tuple(rng.randrange(1,prime) for _ in range(4))
            data=evaluate(point)
            if data is None:
                continue
            for row in point_block(point,data,mons):
                if (sum(a*b for a,b in zip(row[:-1],solution))-row[-1])%prime:
                    valid=False
                    break
            if not valid:
                break
        ans["independent_100_fibers_pass"]=valid
        (HERE/f"{prefix}current_degree{degree}_candidate.pickle").write_bytes(pickle.dumps(
            dict(prime=prime,degree=degree,monomials=mons,solution=solution,points=points)))
        (HERE/f"{prefix}current_degree{degree}.json").write_text(json.dumps(ans,indent=2)+"\n")
    print(json.dumps(ans),flush=True)
    return ans

if __name__=="__main__":
    for degree in list(map(int,sys.argv[1:])) or [0,1,2,3]:
        run(degree)
