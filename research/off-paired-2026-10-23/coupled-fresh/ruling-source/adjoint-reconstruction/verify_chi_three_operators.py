"""Exact normalized chi operators, fiber Cartan corrections and adjoints.

The cubic box is checked through its universal root-residue proof and the
commuting Cartan expansion, rather than a large unstructured third derivative.
"""
import json
from pathlib import Path
import sympy as s

c,d,e,q,b=s.symbols('c d e q b')
P=b**4+(c*q*q+e*q+1)*b*b+d*q**4*b+q**6
Pb=s.diff(P,b)
def der(f,v):return s.diff(f,v)-s.diff(P,v)*s.diff(f,b)/Pb
def remzero(f):
 num=s.cancel(f).as_numer_denom()[0]
 return s.rem(num,P,b)==0
chi=b/q  # The fixed nonzero normalization b0=i is immaterial here.
cc=der(chi,c)
def AF(f):return-c*der(f,c)/3-2*d*der(f,d)/3-e*der(f,e)/6
def BF(f):return-c*der(f,c)/3-d*der(f,d)/6-e*der(f,e)/6
def TF(f):return-c*der(f,c)/3-d*der(f,d)/6-2*e*der(f,e)/3
checks=[]
def check(name,condition):
 assert condition,name
 checks.append(name)
check('PD exact fiber primitive',remzero(der(der(chi,d),d)-AF(cc)+cc/3-der(q*cc/6,q)))
check('PE exact fiber primitive',remzero(der(der(chi,e),e)-TF(cc)-cc/6+der(q*cc/3,q)))

# Exact commuting-operator Cartan polynomial, including all coefficient shifts.
aa,bb,tt,rr=s.symbols('Aop Bop Top Rq')
U=(aa+bb)*tt/6-aa*bb/3
V=tt/36-(aa+bb)/18
check('P3 full Cartan correction',s.expand((aa+rr/6)*(bb+rr/6)*(tt-rr/3)-aa*bb*tt-rr*U-rr**2*V+rr**3/108)==0)

# Literal universal box monomials, all of the same parameter order.
A,B,C,D,E,T=s.symbols('A B C D E T')
rootpoly=B*b**4+(C*q*q+E*q+T)*b*b+D*q**4*b+A*q**6
mon={x:s.diff(rootpoly,x)for x in(A,B,C,D,E,T)}
check('literal universal D²−AC monomial equality',s.expand(mon[D]**2-mon[A]*mon[C])==0)
check('literal universal E²−CT monomial equality',s.expand(mon[E]**2-mon[C]*mon[T])==0)
check('literal universal ABT−C³ monomial equality',s.expand(mon[A]*mon[B]*mon[T]-mon[C]**3)==0)

# Formal Green identities on arbitrary functions, with dc dd de density.
x=s.Function('chi')(c,d,e)
f=s.Function('f')(c,d,e)
g=s.Function('g')(c,d,e)
h=s.Function('h')(c,d,e)
avec=[-c/3,-2*d/3,-e/6]
bvec=[-c/3,-d/6,-e/6]
tvec=[-c/3,-d/6,-2*e/3]
coords=[c,d,e]
def act(v,F):return sum(vv*s.diff(F,xx)for vv,xx in zip(v,coords))
def vadd(*vs):return[sum(v[i]for v in vs)for i in range(3)]
def vscale(F,v):return[F*vv for vv in v]
def div(v):return sum(s.diff(vv,xx)for vv,xx in zip(v,coords))
def Ad(F):return act(avec,F)
def Bd(F):return act(bvec,F)
def Td(F):return act(tvec,F)
def pE(F):return s.diff(F,e,2)-Td(s.diff(F,c))-s.diff(F,c)/6
def pD(F):return s.diff(F,d,2)-Ad(s.diff(F,c))+s.diff(F,c)/3
def p3(F):return Ad(Bd(Td(F)+F/2)-(Td(F)+F/2)/2)-s.diff(F,c,3)
def pEs(F):return s.diff(F,e,2)-s.diff(Td(F)-4*F/3,c)
def pDs(F):return s.diff(F,d,2)-s.diff(Ad(F)-5*F/6,c)
def p3s(F):return s.diff(F,c,3)-(Ad(Bd(Td(F)-5*F/3)-(Td(F)-5*F/3)/6)-s.Rational(7,6)*(Bd(Td(F)-5*F/3)-(Td(F)-5*F/3)/6))
BE=vadd([0,0,f*s.diff(x,e)-s.diff(f,e)*x],vscale(-f*s.diff(x,c),tvec),[(Td(f)-4*f/3)*x,0,0])
BD=vadd([0,g*s.diff(x,d)-s.diff(g,d)*x,0],vscale(-g*s.diff(x,c),avec),[(Ad(g)-5*g/6)*x,0,0])
Ast_h=-Ad(h)+7*h/6
Bst_Ast_h=-Bd(Ast_h)+Ast_h/6
BT_x=Td(x)+x/2
BB_BT_x=Bd(BT_x)-BT_x/2
B3=vadd(vscale(h*BB_BT_x,avec),vscale(Ast_h*BT_x,bvec),vscale(Bst_Ast_h*x,tvec),[-h*s.diff(x,c,2)+s.diff(h,c)*s.diff(x,c)-s.diff(h,c,2)*x,0,0])
check('PE full Green current',s.expand(f*pE(x)-pEs(f)*x-div(BE))==0)
check('PD full Green current',s.expand(g*pD(x)-pDs(g)*x-div(BD))==0)
check('P3 full Green current',s.expand(h*p3(x)-p3s(h)*x-div(B3))==0)
check('P3 adjoint constant',s.simplify(p3s(s.Integer(1))-s.Rational(35,108))==0)

out={'status':'exact source-current generator, not a primitive','checks':checks,
 'count':len(checks),'source_equation':'PE* f+PD* g+P3* h=−partial_e² Hsrc',
 'infinity':'chi retains its fourth-order infinity second-kind poles; all operators and Cartan primitives are literal rational expressions',
 'certificate':False}
Path(__file__).with_name('chi-three-operator-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(f'Passed {len(checks)} exact chi-box, Cartan and Green-current checks')
