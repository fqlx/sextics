#!/usr/bin/env python3
"""Exact modular evaluation of the full source-bound normalized H=K/v.

No physical source trace is taken. Full i/J/w coordinate derivatives are
computed with total-order-three jets, before point specialization.
"""
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
GM=HERE.parent/'genus4-gm-independent'


def make_mod(prime):
    class Mod(int):
        def __new__(cls,x=0):
            if isinstance(x,Fraction):
                x=x.numerator*pow(x.denominator,-1,prime)
            return int.__new__(cls,int(x)%prime)
        @property
        def denominator(self):return 1
        @property
        def numerator(self):return int(self)
        def __add__(self,b):return Mod(int(self)+int(b))
        __radd__=__add__
        def __neg__(self):return Mod(-int(self))
        def __sub__(self,b):return Mod(int(self)-int(b))
        def __rsub__(self,b):return Mod(int(b)-int(self))
        def __mul__(self,b):return Mod(int(self)*int(b))
        __rmul__=__mul__
        def __truediv__(self,b):return Mod(int(self)*pow(int(b),-1,prime))
        def __rtruediv__(self,b):return Mod(int(b)*pow(int(self),-1,prime))
        def __pow__(self,n):return Mod(pow(int(self),int(n),prime))
    return Mod


class ActualH:
    def __init__(self,prime=1009,i0=2,J0=1,order=3):
        self.prime=prime
        self.M=make_mod(prime)
        sp=importlib.util.spec_from_file_location('h_jets_'+str(id(self)),ROOT/'audit/ruling/verify_actual_lifts_fraction.py')
        self.jm=importlib.util.module_from_spec(sp);sp.loader.exec_module(self.jm)
        self.jm.Q=self.M;self.jm.ORDER=order
        self.Jet=self.jm.Jet;self.eval=self.jm.evaluate;self.var=self.jm.variable
        self.i=self.var(self.M(i0),0);self.J=self.var(self.M(J0),1)
        self.u=self.J/self.i**2
        pot=json.loads((GM/'cubic-residue-potentials-results.json').read_text())
        self.source_sha=pot['source_sha256']
        rec=pot['actual_Ssrc_residue']
        self.pot={key:[self.eval(x,{'u':self.u})for x in rec[key]]for key in
                  ['PE_residue_f_coefficients','PD_residue_g_coefficients','CRT_factor_coefficients']}
        data=json.loads((GM/'actual-polynomial-moment-preimages.json').read_text())
        self.mom={key:(rec['i_weight'],[self.eval(x,{'u':self.u})for x in rec['coefficients']])
                  for key,rec in data['moment_preimages'].items()}
        herm=json.loads((HERE.parent/'ruling-source/adjoint-reconstruction/n-only-hermite-results.json').read_text())
        self.herm={}
        env={'u':self.Jet(self.u.value)}
        for key,rec in herm['components'].items():
            weight=int(key.split('^')[1])
            self.herm[weight]=([self.eval(x,env).value for x in rec['polynomial_primitive_coefficients']],
                              [(z['denominator_power'],[self.eval(x,env).value for x in z['numerator_coefficients']])
                               for z in rec['proper_primitive_terms']])
    def poly(self,ar,w):
        out=self.Jet()
        for x in reversed(ar):out=out*w+x
        return out
    def polyval(self,ar,w):
        out=self.M(0)
        for x in reversed(ar):out=out*w+x
        return out
    def point(self,w0,details=False):
        M=self.M;i=self.i;J=self.J;u=self.u
        w=self.var(M(w0),2)
        T=1+w**3;N=9*w*w-16*u*T
        L=256*T**5*N+729*i**6*u*w**6
        v=64*u*w*N*T*T/(9*L)
        vi,vj,vw=[v.partial(k)for k in range(3)]
        A=lambda x:x.partial(0)-vi/vw*x.partial(2)
        B=lambda x:x.partial(1)-vj/vw*x.partial(2)
        Z=lambda x:v/vw*x.partial(2)
        D=lambda x:6*Z(x)-2*i*A(x)-2*J*B(x)
        LE=lambda x:D(D(x)+x)+A(Z(x)+D(x)/2+2*x)
        LD=lambda x:4*J*B(B(x))+2*B(x)+A(Z(x)+J*B(x)+x)
        def L3(x):
            inner=Z(Z(x)+D(x)/2+5*x)
            return A(A(A(x)))+v*(Z(inner)+J*B(inner)+2*inner)
        f,g,crt=[self.poly(self.pot[name],w)for name in
                 ['PE_residue_f_coefficients','PD_residue_g_coefficients','CRT_factor_coefficients']]
        m=(18*w-48*u*w*w)/N
        src=v*v/vw*54*w*T/(i*u*N)
        F=v*v/vw*f*m/i;G=v*v/vw*g*m
        t=i**-4*w*T*L*crt
        ap=-vi/(v*v);bp=-vj/(v*v)
        ell=6/v+2*i*vi/(v*v)+2*J*vj/(v*v)
        ES=lambda x:ell*(D(x)-5*x)-2*i*(ell*x).partial(0)-2*J*(ell*x).partial(1)
        EE=lambda x:ES(x)+ap*(Z(x)+D(x)/2-2*x)+((1/v+ell/2)*x).partial(0)
        ED=lambda x:4*J*(bp*B(x)+(bp*x).partial(1))+2*bp*x+ap*(Z(x)+J*B(x))+((1/v+J*bp)*x).partial(0)
        E3=lambda x:ap*A(A(x))+(ap*A(x)).partial(0)+(ap*x).partial(0).partial(0)
        tt=Z(t)+D(t)/2+5*t
        woverv=v*(Z(tt)+J*B(tt)+2*tt)
        ctot=ES(src)-EE(F)-ED(G)-E3(v*t)-woverv
        pn=M(0);nv=N.value;wv=M(w0);iv=i.value
        for weight,(pol,proper)in self.herm.items():
            pp=self.polyval(pol,wv)
            for power,ar in proper:pp+=self.polyval(ar,wv)/nv**power
            pn+=iv**weight*pp
        orig=pn+ctot.value
        Q={key:i**weight*self.poly(ar,w)for key,(weight,ar)in self.mom.items()}
        qinf=-729*i**4*w/(440*J)-27*i**3*w*w/(10*J)-5103*i**5*w/(3040*J*J)
        normal=orig+LE(Q['QF']).value+LD(Q['QG']).value+L3(Q['QH_minus']+Q['QH_plus']).value-LD(qinf).value
        if not details:return int(normal)
        return {'H':int(normal),'H_original':int(orig),'v':int(v.value),'v_w':int(vw.value),
                'f':int(1/v.value),'f_w':int(-vw.value/(v.value*v.value)),
                'N0':int(N.value),'T':int(T.value),'L0':int(L.value)}


if __name__=='__main__':
    import time
    started=time.monotonic()
    h=ActualH()
    vals=[]
    for w in [1,3,4,5]:vals.append({'w':w,**h.point(w,True)})
    hh=ActualH(order=4)
    assert hh.point(3)==vals[1]['H']
    out={'source_sha256':h.source_sha,'prime':1009,'i':2,'J':1,'values':vals,
         'check':'full-coordinate jets at total orders3and4 agree atw3',
         'normalization':'originalH+LEQF+LDQG+L3(QHminus+QHplus)-LDQDinf; no constant gauge or trace',
         'scope':'Source evaluation for complete rational primitive construction; no primitive or exclusion claimed',
         'elapsed_seconds':time.monotonic()-started}
    path=HERE/'actual-h-modular-results.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
