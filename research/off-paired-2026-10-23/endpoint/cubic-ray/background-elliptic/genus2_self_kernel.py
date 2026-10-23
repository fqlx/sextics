"""Exact genus-two self-correspondence kernel with all parameter columns.

The globally defined meromorphic one-form supplies a closed exact two-form.
No holomorphic-residue extension or immutable-source match is asserted.
"""
import json
from pathlib import Path
import sympy as S

P,q,D,B,Y,w=S.symbols('P q D B Y w',nonzero=True)
f=lambda t:(D+B*t)**2-4*t**6
fp,fq=f(P),f(q)
checks=[]
def check(name,value):
    assert S.cancel(value)==0,(name,S.factor(value))
    checks.append(name)
def quotient(num):
    out,rem=S.div(S.Poly(S.expand(num),P),S.Poly(P-q,P))
    assert S.cancel(rem.as_expr())==0
    return out.as_expr()

data=json.loads((Path(__file__).parents[2]/'reconstructed-connection.json').read_text())
local={'H':D,'C':B,'p':P}
mh=[S.sympify(t,locals=local) for t in data['H']['columns'][0]]
rh=sum(S.sympify(t,locals=local)*P**j for j,t in enumerate(data['H']['primitives'][0]))
Delta=4*B**6-729*D**4
check('stored-Dwork-source-column',
      -(D+B*P)-fp*sum(m*P**j for m,j in zip(mh,[0,1,3,4]))
       -S.diff(rh,P)*fp+rh*S.diff(fp,P)/2)

tau=w/((P-q)*Y)
vq=[8*q**4,4*q**3,-4*q,-8]
L=3*D+2*B*q
ad=[S.factor(-(2*B*fq*m+q*v)/L) for m,v in zip(mh,vq)]
ab=[S.factor(q*a+fq*m) for a,m in zip(ad,mh)]
N=quotient(P*fq-q*fp)
AD=S.factor(-(N+2*B*fq*rh)/L)
AB=S.factor(q*AD+fq*rh)
TD=quotient((D+B*q)*fp-fq*(D+B*P))
TB=quotient(q*(D+B*q)*fp-fq*P*(D+B*P))
for name,poly,rows,primitive in [('D',TD,ad,AD),('B',TB,ab,AB)]:
    check('literal-normalfunction-'+name+'-column',
       poly-fp*sum(m*P**j for m,j in zip(rows,[0,1,3,4]))
           -S.diff(primitive,P)*fp+primitive*S.diff(fp,P)/2)
    assert not any(S.denom(S.cancel(m)).has(q) for m in rows)
    checks.append('apparent-normalizer-cancels-'+name)
mh3=[S.sympify(t,locals=local) for t in data['H']['columns'][2]]
mc3=[S.sympify(t,locals=local) for t in data['C']['columns'][2]]
for i in range(4):
    check('paired-infinity-D-row-'+str(i),S.Poly(S.cancel(ad[i]),q).coeff_monomial(q*q)-4*mh3[i])
    check('paired-infinity-B-row-'+str(i),S.Poly(S.cancel(ab[i]),q).coeff_monomial(q*q)-4*mc3[i])
eps=S.symbols('eps',nonzero=True)
assert S.rem(S.Poly(S.together(-eps-4/eps)*eps,eps),S.Poly(eps*eps+4,eps)).as_expr()==0
checks.append('literal-two-infinity-residue-cancellation')

# Moving-pole column, with the exact primitive -Y/[w(P-q)].
Nq=S.diff(fq,q)*(P-q)/2+fq+S.diff(fp,P)*(P-q)/2-fp
check('literal-moving-q-column',Nq-(P-q)**2*sum(v*P**j for v,j in zip(vq,[0,1,3,4])))
check('parameter-difference-identity',
      quotient(q*(D+B*q)*fp-fq*P*(D+B*P))
       -q*TD+fq*(D+B*P))

# The full one-form, not only its fiberwise compact projection, is used.
# This polynomial Euler check implies 3D*tau_D+2B*tau_B+q*tau_q=-dP(P*tau).
total_weight=3*D*S.diff(tau,D)+2*B*S.diff(tau,B)+q*S.diff(tau,q)+P*S.diff(tau,P)
total_weight+=3*w*S.diff(tau,w)+3*Y*S.diff(tau,Y)+tau
check('full-kernel-Euler-one-form',total_weight)

# Klein polar and the explicit rational potential K supplied by the parent.
F2=2*D**2+2*D*B*(P+q)+2*B**2*P*q-8*P**3*q**3
check('Klein-polar-diagonal',F2.subs(P,q)-2*fq)
check('Klein-polar-divided-difference',
      F2-2*fq-(P-q)*S.diff(fq,q)+8*q**3*(P-q)**2*(P+2*q))
# Clear 4(P-q)^2Yw in B-dqK+2omega1*Omega3+4omega0*Omega4.
Knumerator=2*fq+(P-q)*S.diff(fq,q)+2*Y*w
check('literal-Klein-Cauchy-identity',
      F2+2*Y*w-Knumerator+8*P*q**3*(P-q)**2+16*q**4*(P-q)**2)

# Exact degree-24 branch: H=r^3D, C=r^2B, p=rq.
r,H,C,z=S.symbols('r H C z',nonzero=True)
graph=8*D**2*C**3+z**3*H**2
check('degree24-graph-branch',graph.subs({H:r**3*D,C:r**2*(-z/2)}))
check('literal-fiber-isomorphism',
      ((H+C*r*q)**2-4*(r*q)**6).subs({H:r**3*D,C:r**2*B})-r**6*fq)
check('rational-graph-scale',((H*B/(D*C))/r).subs({H:r**3*D,C:r**2*B})-1)
CH,Cq,Cz=S.symbols('CH Cq Cz')
GH=16*D*C**3+24*D*D*C*C*CH+2*z**3*H
Gq=24*D*D*C*C*Cq
Gz=-96*D*z**5*C**3+24*D*D*C*C*Cz+3*z*z*H*H
check('full-physical-graph-H-jet',S.diff(graph,H)+S.diff(graph,D)+CH*S.diff(graph,C)-GH)
check('full-physical-graph-q-jet',Cq*S.diff(graph,C)-Gq)
check('full-physical-graph-z-jet',S.diff(graph,z)-6*z**5*S.diff(graph,D)+Cz*S.diff(graph,C)-Gz)

out={
 'status':'Exact globally defined genus-two self kernel and all parameter columns; source closure open',
 'constant_scope':'fixed characteristic-zero k; k=C for full contract',
 'check_count':len(checks),'checks':checks,
 'curve':'Y^2=(D+B*P)^2-4P^6, w^2=(D+B*q)^2-4q^6',
 'basis':[0,1,3,4],
 'normalfunction':'tau=w*dP/[(P-q)Y], residues +1,-1; use the full absolute differential d tau',
 'columns':{
    'D':{'compact_numerator_over_w':[str(m) for m in ad],'exact_primitive':'AD/(w*Y)','AD':str(AD)},
    'B':{'compact_numerator_over_w':[str(m) for m in ab],'exact_primitive':'AB/(w*Y)','AB':str(AB)},
    'q':{'compact_numerator_over_w':[str(m) for m in vq],'exact_primitive':'-Y/[w*(P-q)]'}},
 'Klein':{'polar':str(F2),
          'Cauchy_one_form':'K=(Y+w)dP/[2Y(P-q)]',
          'bidifferential':'Berg=(F2+2Yw)dP*dq/[4(P-q)^2Yw]',
          'literal_relation':'Berg=partial_q(K_P)*dP*dq-2*omega1(P)*Omega3(q)-4*omega0(P)*Omega4(q); exterior d(K) has NEGATIVE q-part in dP wedge dq order'},
 'paired_infinity_normalization':{
    'two_form':'Khat=tau wedge dq-4*omega3(P) wedge Omega2(q)',
    'D_q2_column':'4*MH*e3','B_q2_column':'4*MC*e3=4*MH*e4',
    'residue':'Both background infinities have zero residue in Khat. Endpoint omega3 is second-kind, and background Omega2 has constant residues.',
    'full_derivative':'dKhat=d(tau) wedge dq-4*d(omega3(P)) wedge Omega2(q)+4*omega3(P) wedge d(Omega2(q))',
    'warning':'The last compensating term is retained with its full compact and exact background columns. This is a correction kernel; no immutable-source match or nonzero H20 residue is asserted.'},
 'graph':{'D':'H-1-z^6','B':'-z/2','equation':str(graph),
          'scale':'r=H*B/(D*C) on the generic graph; r^3=H/D,r^2=C/B',
          'relative_isomorphism':'p=r*P,Zp=r^3*Y',
          'full_basis_pullback':'omega_j(ep)=r^(j-2)*Omega_j(bg)+r^(j-3)*P^(j+1)*dr/Y',
          'full_kernel_pullback':'tau_ep=tau_bg+[P*w/((P-q)*Y)]dlogr, when the moving pole is r*q',
          'qH':str(-GH/Gq),'qz':str(-Gz/Gq),
          'full_scale_jet':'dlogr=dH/H+dz/z-(dH-6z^5dz)/D-(CH*dH+Cq*dq+Cz*dz)/C; use dq=qH*dH+qz*dz on graph',
          'infinity_horizontal_identity':'omega2(ep)=Omega2(P)+(P^3/Y(P))dlogr; background Euler uses q^3/w(q), the same rational function at the OTHER point, equal only on P=q'},
 'physical_parameter_transport':'D=H-1-z^6,B=-z/2: partial_H=partial_D,partial_z=-6z^5partial_D-partial_B/2, plus full q and graph-scale derivatives',
 'gap':'d tau is globally closed and exact as a meromorphic two-form. No claim that its relative holomorphic part alone extends, or that it equals the actual target/source residue. The full coupled forcing and background omega2 row still must match.',
}
Path(__file__).with_name('genus2-self-kernel-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed',len(checks),'exact full genus-two kernel, parameter-column and graph identities')
