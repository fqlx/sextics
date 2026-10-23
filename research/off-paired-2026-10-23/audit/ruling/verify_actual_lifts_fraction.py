#!/usr/bin/env python3
"""Independent exact-point audit of physical ruling lifts and adjoints.

No primary code is imported or executed. The lift is reconstructed by solving
the six coefficient equations over exact second-order Taylor jets, rather than
using the submitted closed formulas. Stored formulas are parsed with a small
AST evaluator and compared, including their first two derivatives.
"""
import ast
from fractions import Fraction as Q
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
ZERO=(0,0,0)
ORDER=2


class Jet:
    def __init__(self,c=0):
        self.c=({e:Q(v) for e,v in c.items() if v} if isinstance(c,dict)
                else ({ZERO:Q(c)} if c else {}))
    @property
    def value(self):return self.c.get(ZERO,Q(0))
    def __add__(self,b):
        b=jet(b);out=dict(self.c)
        for e,v in b.c.items():
            out[e]=out.get(e,Q(0))+v
            if not out[e]:del out[e]
        return Jet(out)
    __radd__=__add__
    def __neg__(self):return Jet({e:-v for e,v in self.c.items()})
    def __sub__(self,b):return self+-jet(b)
    def __rsub__(self,b):return jet(b)+-self
    def __mul__(self,b):
        b=jet(b);out={}
        for e,v in self.c.items():
            for f,w in b.c.items():
                g=tuple(x+y for x,y in zip(e,f))
                if sum(g)<=ORDER:out[g]=out.get(g,Q(0))+v*w
        return Jet(out)
    __rmul__=__mul__
    def inverse(self):
        a=self.value
        assert a,'singular jet inverse'
        n=(self-a)*(1/a)
        out=Jet(1);term=Jet(1)
        for _ in range(ORDER):
            term=-term*n;out=out+term
        return out*(1/a)
    def __truediv__(self,b):return self*jet(b).inverse()
    def __rtruediv__(self,b):return jet(b)*self.inverse()
    def __pow__(self,n):
        assert isinstance(n,int)
        if n<0:return self.inverse()**(-n)
        out=Jet(1);factor=self
        while n:
            if n&1:out=out*factor
            n//=2
            if n:factor=factor*factor
        return out
    def partial(self,i):
        out={}
        for e,v in self.c.items():
            if e[i]:
                f=list(e);f[i]-=1;out[tuple(f)]=v*e[i]
        return Jet(out)
    def first(self):return {e:v for e,v in self.c.items() if sum(e)<=1}


def jet(x):return x if isinstance(x,Jet) else Jet(x)


def variable(v,i):
    e=[0,0,0];e[i]=1
    return Jet({ZERO:Q(v),tuple(e):Q(1)})


def evaluate(text,env):
    def visit(n):
        if isinstance(n,ast.Constant):
            assert type(n.value) is int
            return Jet(n.value)
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp):
            if isinstance(n.op,ast.USub):return -visit(n.operand)
            assert isinstance(n.op,ast.UAdd);return visit(n.operand)
        assert isinstance(n,ast.BinOp)
        if isinstance(n.op,ast.Pow):
            exponent=visit(n.right)
            assert set(exponent.c)<=set([ZERO]) and exponent.value.denominator==1
            return visit(n.left)**int(exponent.value)
        a,b=visit(n.left),visit(n.right)
        if isinstance(n.op,ast.Add):return a+b
        if isinstance(n.op,ast.Sub):return a-b
        if isinstance(n.op,ast.Mult):return a*b
        assert isinstance(n.op,ast.Div);return a/b
    return visit(ast.parse(text,mode='eval').body)


def solve(matrix,rhs):
    n=len(rhs);a=[list(row)+[b] for row,b in zip(matrix,rhs)]
    determinant=Q(1)
    for i in range(n):
        pivot=next(j for j in range(i,n) if a[j][i].value)
        if pivot!=i:a[i],a[pivot]=a[pivot],a[i];determinant=-determinant
        d=a[i][i];determinant*=d.value
        a[i]=[x/d for x in a[i]]
        for j in range(n):
            if j!=i:
                c=a[j][i];a[j]=[x-c*y for x,y in zip(a[j],a[i])]
    return [a[i][-1] for i in range(n)],determinant


def main():
    data_path=HERE.parents[1]/'coupled-fresh/infinity-horizontal/actual-ruling-adjoints.json'
    data=json.loads(data_path.read_text())
    newer_path=HERE.parents[1]/'coupled-fresh/ruling-source/physical-source-adjoints.json'
    newer=json.loads(newer_path.read_text())
    labels=['R','S','z','alpha','u','v'];checks=[];points=[]
    def check(name,condition):
        assert condition,name
        checks.append(name)
    # R=r²,S=s²,k^6=RS. Choose rational points on that cover, not
    # arbitrary inconsistent specializations of four formal symbols.
    for index,(r6,s6,z0,k0) in enumerate([
            (1,1,Q(1),1),(64,1,Q(2),2),(1,64,Q(1,2),2),
            (64,729,Q(-1),6),(729,4096,Q(3,2),12)]):
        R,S,z=[variable(x,i) for i,x in enumerate([r6,s6,z0])]
        k=Jet({ZERO:Q(k0),(1,0,0):Q(k0,6*r6),(0,1,0):Q(k0,6*s6),
               (2,0,0):-Q(5*k0,72*r6*r6),(0,2,0):-Q(5*k0,72*s6*s6),
               (1,1,0):Q(k0,36*r6*s6)})
        env=dict(R=R,S=S,z=z,k=k)
        check(f'{index}: algebraic cover jet',not (k**6-R*S).c)
        A=1+R;B=1+S;C=k/3;D=z*k/2;E=z/2;T=1+z**6
        # Unknowns are VR,VS,Vz,alpha,u,v. These are the six actual
        # coefficient equations VQ=P+alpha Q-X_tor Q, independently
        # written directly from Q. wa=u+v,wb=-u+v,wq=2v/3.
        mat=[
            [Jet(1),Jet(),Jet(),-A,2*A,2*A],
            [Jet(),Jet(1),Jet(),-B,-2*B,2*B],
            [C/(6*R),C/(6*S),Jet(),-C,Jet(),4*C/3],
            [D/(6*R),D/(6*S),D/z,-D,D,5*D/3],
            [Jet(),Jet(),Jet(Q(1,2)),-E,Jet(),2*E/3],
            [Jet(),Jet(),6*z**5,-T,Jet(),Jet()]]
        rhsT=[Jet(),Jet(),Jet(),Jet(),Jet(),Jet(1)]
        rhsD=[Jet(),Jet(),D/(2*A),Jet(1),Jet(),Jet()]
        Cp=C-D**2/(4*A)
        rhsE=[Jet(),Jet(),Jet(),Jet(),Jet(1),Jet()]
        rhsW=[Jet(),Jet(),Jet(),Jet(),Jet(1),E/(2*Cp)]
        sols={}
        newlabels={'LT':'T_lift','LDshear':'shear_lift','LE':'E_lift','LW':'W_lift'}
        for name,rhs in [('LT',rhsT),('LDshear',rhsD),('LE',rhsE),('LW',rhsW)]:
            sol,det=solve(mat,rhs);sols[name]=sol
            if name in data:
                submitted=[evaluate(data[name][key],env) for key in labels]
                check(f'{index}: old {name} coefficient equations through second jet',
                      all(not (a-b).c for a,b in zip(sol,submitted)))
            submitted=[evaluate(newer[newlabels[name]][key],env) for key in labels]
            check(f'{index}: new {name} coefficient equations through second jet',
                  all(not (a-b).c for a,b in zip(sol,submitted)))
        VT,VD=sols['LT'],sols['LDshear']
        def divergence(V):
            # Constant factor in mu is irrelevant: mu=1/(108 k^5).
            return sum((V[i].partial(i) for i in range(3)),Jet())-Q(5,6)*(V[0]/R+V[1]/S)
        def action(V,F):return sum((V[i]*F.partial(i) for i in range(3)),Jet())
        cT=-VT[3]-VT[4]+Q(7,3)*VT[5]
        check(f'{index}: T lift q eta torus scalar equals 2v',not (cT-2*VT[5]).c)
        M=divergence(VT)+cT
        storedM=evaluate(data['M_T'],env)
        check(f'{index}: first density adjoint value and gradient',M.first()==storedM.first())
        check(f'{index}: new T density adjoint value and gradient',M.first()==evaluate(newer['hT'],env).first())
        h2=A*(T-E**2/(4*Cp))/(B*Cp)
        check(f'{index}: h squared full second jet',not (h2-evaluate(data['h_squared'],env)).c)
        positive=(action(VD,M)+M*divergence(VD)+M*action(VD,h2)/(2*h2)).value
        stored=evaluate(data['remaining_beta_coefficient_over_h'],env).value
        check(f'{index}: JSON stores negative of physical source residual',stored==-positive)
        check(f'{index}: displayed residual is nonzero at point',bool(positive))
        check(f'{index}: new JSON T source residual uses positive convention',positive==evaluate(newer['gT_over_kappa'],env).value)
        LE,LW=sols['LE'],sols['LW']
        hE=divergence(LE)-LE[3]-LE[4]+Q(5,3)*LE[5]
        check(f'{index}: E density adjoint value and gradient',hE.first()==evaluate(newer['hE'],env).first())
        m=2*Cp/D
        check(f'{index}: translation to shear normalization ratio',not (m-evaluate(newer['kappa_E_over_kappa_S'],env)).c)
        translated=m*hE
        gE=-(action(LW,translated)+translated*divergence(LW)+translated*action(LW,h2)/(2*h2)).value
        check(f'{index}: new JSON E source residual convention',gE==evaluate(newer['gE_over_kappa'],env).value)
        points.append({'R':str(r6),'S':str(s6),'z':str(z0),'k':str(k0),
            'lift_matrix_determinant':str(det),'M_T':str(M.value),
            'h_squared':str(h2.value),'source_residual_beta_over_h':str(positive),
            'stored_negative_adjoint':str(stored),'hE':str(hE.value),
            'E_W_source_residual_beta_over_h':str(gE)})
    result={'status':'passed','count':len(checks),'checks':checks,'points':points,
        'arithmetic':'independent standard-library Fraction second-order jets; independent 6x6 solve from six coefficient equations',
        'density':'dr dk dz/(9r)=dR dS dz/(108 k^5), k^6=RS; log-gradient (-5/(6R),-5/(6S),0)',
        'sign':'For source -nabla_T(q eta_b) and beta shear q eta_b=-h nabla_S beta+fiber-exact, physical residual is +div_mu(h M_T VD) beta. JSON remaining_beta_coefficient_over_h stores its negative divided by h.',
        'scope':'Five exact points and full second jets check submitted lift formulas and adjoints locally; this is not a global identity proof or a primitive. Nonzero residual concerns this constructed current only.'}
    (HERE/'actual-lifts-fraction-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
