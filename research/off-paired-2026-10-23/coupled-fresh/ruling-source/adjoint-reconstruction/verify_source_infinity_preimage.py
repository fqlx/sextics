#!/usr/bin/env python3
"""Exact source-specific infinity preimage after properizing the moments.

This is a literal lift change, not a polynomial-degree search. It removes
the two positive infinity coefficients of the actual K/v, at the cost of
higher artificial fold poles. Every compact/infinity source stays present.
"""
from pathlib import Path
import json
import sympy as s

HERE=Path(__file__).resolve().parent
i,j,w=s.symbols('i J w')
K=s.QQ.frac_field(i,j)
def P(e):return s.Poly(e,w,domain=K)
T=P(1+w**3);N=P(9*i**2*w**2-16*j*(1+w**3))
L=256*T**5*N+P(729*i**6*j*w**6)
C=N*T*L+P(w)*N.diff()*T*L+2*P(w)*N*T.diff()*L-P(w)*N*T*L.diff()
def dx(p,x):return P(s.diff(p.as_expr(),x))
ai=P(w)*T*((dx(N,i)-N.mul_ground(K.from_sympy(2/i)))*L-N*dx(L,i))
bj=P(w)*T*((dx(N,j)+N.mul_ground(K.from_sympy(1/j)))*L-N*dx(L,j))
zw=P(w)*N*T*L
checks=[]
def check(name,x):
    assert x,name
    checks.append(name)
for label,num,lead in [
 ('vi/vw',ai,w/(4*i)),('vJ/vw',bj,-w/(8*j)),('Z_w',zw,-w/8),
 ('D_w',6*zw+ai.mul_ground(K.from_sympy(2*i))+bj.mul_ground(K.from_sympy(2*j)),-w/2)]:
    rem=num-P(lead)*C
    check(label+' error O(w^-2)',rem.is_zero or rem.degree()-C.degree()<=-2)
def Ainf(x):return s.diff(x,i)-w/(4*i)*s.diff(x,w)
def Binf(x):return s.diff(x,j)+w/(8*j)*s.diff(x,w)
def Zinf(x):return -w*s.diff(x,w)/8
def Dinf(x):return -2*i*s.diff(x,i)-2*j*s.diff(x,j)-w*s.diff(x,w)/2
Ph=-27*i**3*w**2/(16*j**2)-243*i**5*w/(128*j**3)
Hplus=s.expand(Dinf(Dinf(Ph)+Ph))
expected=-81*i**3*w**2/(8*j**2)-15309*i**5*w/(512*j**3)
check('actual source positive infinity coefficients',s.cancel(Hplus-expected)==0)
Qinf=-9*i**6*w**2/(77*j**2)-567*i**8*w/(5704*j**3)
image=s.expand(Ainf(Ainf(Ainf(Qinf))))
check('explicit cubic infinity preimage',s.cancel(image-Hplus)==0)
QDinf=-27*i**3*w**2/(10*j)-5103*i**5*w/(3040*j**2)-729*i**4*w/(440*j)
imageD=s.expand(4*j*Binf(Binf(QDinf))+2*Binf(QDinf)+Ainf(Zinf(QDinf)+j*Binf(QDinf)+QDinf))
check('explicit quadratic infinity preimage',s.cancel(imageD-Hplus)==0)
out={
 'source_sha256':'d725307869fcf3a2f064a0a6616eee78ea59f74dd3305fcb1d2408d3018f25b5',
 'checks':len(checks),'identities':checks,
 'prerequisite':'Use actual source-bound F/G/H potential moments after subtracting their exact polynomial parts. The source h remains physical.',
 'source_moment_polynomial_primitive':str(Ph),
 'actual_H_positive_polynomial_part':str(Hplus),
 'Qinf':str(Qinf),
 'preferred_QDinf':str(QDinf),
 'exact_lift':'Preferred: G -> G+v Z QDinf; K/v -> K/v-LD QDinf. Cubic alternative: Hpot -> Hpot+v Z Qinf; K/v -> K/v-L3 Qinf.',
 'consequence':'Actual new K/v is O(1) at infinity. Its remaining constant is removable by the allowed K->K+vC(i,J) gauge, giving O(w^-1).',
 'fold_behavior':'Full cubic-moment properization itself generally raises K/v from fold order three to five, since QH has a nonzero linear Morse jet. Preferred LD QDinf has order two and does not raise this existing bound. After full properization the safe bound is s^-5,s^-3,s^-1 for K/v, source pole order four, and a rational fold current with denominator Ccrit^3. The cubic alternative Qinf also has bound five.',
 'limitation':'This does not make H polynomial in f=1/v, does not integrate the compact source, and is not a sextic certificate.',
 'certificate':False,
}
(HERE/'source-infinity-preimage-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
