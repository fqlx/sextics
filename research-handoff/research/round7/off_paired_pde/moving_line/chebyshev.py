from pathlib import Path
import pickle,json,sympy as sy
import sys
sys.path.insert(0,str(Path(__file__).parents[1]))
import search as z
k,q,h=sy.symbols('k q h');ss,tt,X,Y,Z,tau=sy.symbols('slope t X Y Z tau')
p=pickle.load(open('/workspace/research/round6/k3_normalform/lambda_gm.pickle','rb'))
kk,qq,hh=tuple(p['symbols'][x]for x in ('k','q','h'))
A,B=[p['scaled'][x].subs({kk:k,qq:q,hh:h}) for x in ('A','B')]
a1=sy.Poly(A,k).coeff_monomial(k);a0=A.subs(k,0)
b2=sy.Poly(B,k).coeff_monomial(k*k);b1=sy.Poly(B,k).coeff_monomial(k);b0=B.subs(k,0)
t=-(a1*ss+b2)/(3*ss**2)
P=9*ss**6+3*a0*ss**4+3*b1*ss**3+a1*b2*ss+b2**2
Tau=sy.cancel(-(t**3+a0*t+b0)/ss**3)
# Universal quotient and differential identities retain the W twist.
assert sy.expand((k**3-3*k)**2-4-(k*k-4)*(k*k-1)**2)==0
assert sy.diff(k**3-3*k,k)==3*(k*k-1)
N,D=sy.fraction(Tau)
root=Path(__file__).parent
(root/'chebyshev_physical.pickle').write_bytes(pickle.dumps({'A':A,'B':B,'coefficients':(a1,a0,b2,b1,b0),'slope_polynomial':P,'t':t,'tau':Tau,'symbols':(k,q,h,ss),'lambda_jets':{x:p['scaled'][x]for x in ('A_lambda','B_lambda')}}))
result={'t':str(t),'slope_polynomial':str(sy.factor(P)),'tau_numerator':str(sy.factor(N)),'tau_denominator':str(sy.factor(D)),'j_elliptic':'16*(tau^2+12)^3/(tau^2-4)^2','quotient':'X=k^3-3*k, Y=(k^2-1)*Z; Y^2=slope^3*(X^2-4)*(X-tau)','differential':'dX/Y=3*dk/Z (relative to q,h,slope)','scope':'Exact incidence and differential identity only. A closed regular odd 2-form and nonzero physical Gysin/source are still required.'}
(root/'chebyshev_physical.json').write_text(json.dumps(result,indent=2)+'\n')
print('P slope degree',sy.degree(P,ss),'terms',len(sy.Poly(P,ss,q,h).terms()))
print('tau numerator degree/terms',sy.total_degree(N),len(sy.Poly(N,ss,q,h).terms()))
print('tau denominator',sy.factor(D))
