#!/usr/bin/env python3
"""Independent exact Theta compact source, descent and density audit."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from verify_connection_fraction import Ring
sys.path.insert(0,str(HERE.parent/'quotient'))
from verify_piola_transfer import LaurentRing


def main():
    checks=[]
    def check(name,a):
        assert not a,(name,a)
        checks.append(name)
    r=Ring(['a','b','q','c','d','e']);p=r.poly
    # Monic weighted-grevlex Groebner generators. Coefficients c,d,e
    # are parameters, so division needs no parameter denominator.
    rules=[((2,0,0),p('a**2+d*a*q+b**2+c*q**2+e*q+1')),
           ((1,1,0),p('a*b-q**3')),
           ((0,3,0),p('b**3+a*q**3+c*b*q**2+d*q**4+e*b*q+b'))]
    def red(a):
        work=dict(a);out={}
        while work:
            ex=max(work,key=lambda e:(3*e[0]+3*e[1]+2*e[2],-e[2],-e[1],-e[0],e[3:]))
            co=work[ex]
            for lead,rule in rules:
                if all(ex[i]>=lead[i] for i in range(3)):
                    mult=tuple(ex[i]-(lead[i] if i<3 else 0) for i in range(6))
                    work=r.add(work,r.scale(r.mul({mult:co},rule),-1))
                    break
            else:
                out=r.add(out,{ex:co});del work[ex]
        return out
    J=p('2*a**2+d*a*q-2*b**2')
    da=p('-a*(2*c*q+d*a+e)-6*b*q**2')
    db=p('b*(2*c*q+d*a+e)+3*q**2*(2*a+d*q)')
    def delta(f):return red(r.add(r.mul(r.diff(f,'a'),da),r.mul(r.diff(f,'b'),db),r.mul(r.diff(f,'q'),J)))
    source=HERE.parents[1]/'coupled-fresh/theta-compact/affine-theta-reduction-results.json'
    raw=source.read_bytes();data=json.loads(raw)
    coeff=[p(s) for s in data['theta_basis_coefficients']]
    basis=[p(s) for s in data['basis']]
    kappa=p(data['kappa'])
    expected_kappa=p('d*((c-d**2/4)**3+8)/16')
    check('kappa normalization',r.add(kappa,r.scale(expected_kappa,-1)))
    Ntheta=r.add(p('2*c*b**3+4*d*b**2*q**2+6*b*q**4+e*a*q**2+e*d*q**3/2'),r.mul(kappa,p('q**2')))
    check('literal generic Omega reduction',red(r.add(Ntheta,r.scale(delta(p(data['theta_exact_primitive'])),-1),r.scale(r.add(*(r.mul(a,b) for a,b in zip(coeff,basis))),-1))))
    Cp=p('c-d**2/4');R4=r.scale(r.mul(Cp,p('c-5*d**2/4')),Q(1,8))
    check('Omega infinity coordinate cancels',r.add(coeff[2],r.mul(R4,coeff[4]),r.scale(r.mul(p('d'),coeff[6]),Q(-1,2))))
    # Generic infinity residues from a projective local series. Use the
    # coefficient ring Q[c,d,e,I]/(I²+1), no numeric specialization.
    rawc=Ring(['c','d','e','I'])
    class ComplexRing(Ring):
        def mul(self,a,b):
            out={}
            for ex,co in rawc.mul(a,b).items():
                ee=ex[:3]+(ex[3]%2,)
                out=self.add(out,{ee:co*((-1)**(ex[3]//2))})
            return out
    cr=ComplexRing(rawc.names);cp=cr.poly
    n=5
    def sa(*args):return [cr.add(*(a[i] for a in args)) for i in range(n)]
    def ss(a,x):return [cr.scale(t,x) for t in a]
    def sm(a,b):return [cr.add(*(cr.mul(a[j],b[i-j]) for j in range(i+1))) for i in range(n)]
    def si(a,inv0):
        b=[inv0]
        for i in range(1,n):b.append(cr.scale(cr.mul(inv0,cr.add(*(cr.mul(a[j],b[i-j]) for j in range(1,i+1)))),-1))
        return b
    def sp(a,k):
        if k<0:return sp(si(a,cp('-I')),-k)
        out=[cp('1')]+[{}]*(n-1)
        for _ in range(k):out=sm(out,a)
        return out
    bs=[cp('I'),cp('I*d/2'),cp('I*(c/2-d**2/8)'),cp('I*(-d*c/4+d**3/16)'),cp('I*(-c**2/8+3*d**2*c/16-5*d**4/128)+e/2')]
    ubminus2b=[cr.scale(v,j-2) for j,v in enumerate(bs)]
    den=sa([cp('2'),cp('d'),{},{},{}],ss(sm(bs,bs),-2))
    invden=si(den,cp('1/4'))
    residue=[]
    words=[(0,0,j) for j in range(5)]+[(1,0,0),(1,0,1),(0,1,0),(0,1,1)]
    ratios=[cp(t) for t in ['0','0','1','0','(c-d**2/4)*(c-5*d**2/4)/8','0','-d/2','0','0']]
    for j,(aa,bb,qq) in enumerate(words):
        power=3*aa+3*bb+2*qq-4
        value={} if power<0 else sm(sm(sp(bs,aa+2*bb+qq-2),ubminus2b),invden)[power]
        residue.append(value)
        check('generic infinity residue of '+data['basis'][j],cr.add(value,cr.scale(cr.mul(cp('-I/2'),ratios[j]),-1)))
    # Source descent c=i e²,d=j e,Jinv=j²,v=e6. All identities below
    # are Laurent polynomial identities, so no branch is chosen numerically.
    gr=LaurentRing(['i','j','e']);gp=gr.laurent
    csub={'a':gr.const(0),'b':gr.const(0),'q':gr.const(0),'c':gp('i*e**2'),'d':gp('j*e'),'e':gp('e')}
    compactindices=[0,1,3,4,5,6,7,8];weights=[1,2,4,5,1,2,4,5]
    desired=[
      '-i*j*(12*i-j**2)*e**6/840','-i*j*(12*i-j**2)*e**6/840',
      '-2*j/21','-j*(44*i-7*j**2)/280','i*(12*i-j**2)*e**6/420',
      '(i*(96*i**2-44*i*j**2+3*j**4)*e**6-2880)/1680',
      '-(456*i-3*j**2-80)/420','-(208*i-9*j**2)/840']
    for j,(index,m) in enumerate(zip(compactindices,weights)):
        out=gr.mul(r.subst(coeff[index],csub,gr),gp('e**'+str(2-m)) if 2-m>=0 else gp('1/e**'+str(m-2)))
        check('descended actual compact coefficient '+str(j),gr.add(out,gr.scale(gp(desired[j]),-1)))
    check('literal finite-section V derivative numerator',red(r.add(p('b*(2*c*q+d*a+e)'),p('-d*q**3-e*b-2*c*b*q'))))
    # Full physical Jacobian; e_i,e_J terms are retained and cancel.
    dr=LaurentRing(['i','j','e','vi','vJ','vw']);dp=dr.laurent
    ei,ej,ew=[dp(s) for s in ['vi/(6*e**5)','vJ/(6*e**5)','vw/(6*e**5)']]
    matrix=[
      [dr.add(dp('e**2'),dr.mul(dp('2*i*e'),ei)),dr.mul(dp('2*i*e'),ej),dr.mul(dp('2*i*e'),ew)],
      [dr.mul(dp('j'),ei),dr.add(dp('e/(2*j)'),dr.mul(dp('j'),ej)),dr.mul(dp('j'),ew)],
      [ei,ej,ew]]
    determinant={}
    for pm in permutations(range(3)):
        term=dr.const((-1)**sum(pm[i]>pm[j] for i in range(3) for j in range(i+1,3)))
        for i in range(3):term=dr.mul(term,matrix[i][pm[i]])
        determinant=dr.add(determinant,term)
    check('full dc dd de Jacobian including transverse e derivatives',dr.add(determinant,dp('-vw/(12*j*e**2)')))
    check('actual forcing density descends rationally',dr.add(dr.mul(determinant,dp('1/e**10')),dp('-vw/(12*j*e**12)')))
    check('kappa over e is rational in v',gr.add(r.subst(kappa,csub,gr),gr.scale(gp('j*e*(e**6*(i-j**2/4)**3+8)/16'),-1)))
    out={'status':'passed','count':len(checks),'checks':checks,
        'compact_basis':['1','q','q^3','q^4-R4*q²','a','a*q+d*q²/2','b','b*q'],
        'compact_gauge_exponents':weights,
        'source_coefficients_in_descended_basis':[s.replace('e**6','v').replace('j**2','J').replace('j**4','J**2') for s in desired],
        'source_density':'S_w=v_w(D-7)K/(12j v²), j²=J; forcing S_w[-Omega_hat+zeta_hat/2+(kappa/e)omega_hat]',
        'finite_section_column':'d_w zeta_hat=(v_w/2v)zeta_hat+(v_w/6v)(j beta_q3+beta_b+2i beta_bq)',
        'source_sha256':hashlib.sha256(raw).hexdigest(),
        'scope':'Exact compact source, infinity residues, gauge and full physical density interface. The generic connection and a solution of the resulting inhomogeneous ODE remain separate; no certificate.'}
    (HERE/'theta-source-interface-fraction-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
