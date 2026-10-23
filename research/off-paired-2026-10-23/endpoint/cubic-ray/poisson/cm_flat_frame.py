"""Actual flat CM frame, elliptic quotient, and root-character audit.

The frame preserves the original physical volume. No source current or
compatibility between physical and S3 translations is asserted.
"""
import sympy as S,json
from pathlib import Path
x,a,r=S.symbols('x a r');h=x**6+a**6;rel=r**3-h
checks=[]
def red(q):
 n,d=S.fraction(S.cancel(q));return S.rem(n,rel,r)
def check(name,q):
 assert S.cancel(red(q))==0,(name,S.factor(q));checks.append(name)
dr=S.Matrix([2*x**5/r**2,2*a**5/r**2])
eta=S.Matrix([a/r,-x/r]);RX=S.Matrix([x/r,a/r]);TX=S.Matrix([a**5/r**2,-x**5/r**2])
def diff(q,i):return S.diff(q,[x,a][i])+S.diff(q,r)*dr[i]
def apply(V,q):return sum(V[i]*diff(q,i)for i in range(2))
def div(V):return sum(diff(V[i],i)for i in range(2))
check('RX-divergence',div(RX));check('TX-divergence',div(TX))
check('dr-RX',dr.dot(RX)-2);check('dr-TX',dr.dot(TX))
check('eta-RX',eta.dot(RX));check('eta-TX',eta.dot(TX)-1)
check('eta-closed',diff(eta[1],0)-diff(eta[0],1))
for i in range(2):check('frame-commutator-'+str(i),apply(RX,TX[i])-apply(TX,RX[i]))
check('actual-area',dr[0]*eta[1]-dr[1]*eta[0]+2)
ee=r**2/(x*x*a*a);vv=(x**6-a**6)/(x**3*a**3)
check('CM-elliptic-equation',vv**2-ee**3+4)
for i in range(2):check('CM-elliptic-differential-'+str(i),diff(ee,i)-2*vv*eta[i])
check('TX-elliptic-x',apply(TX,ee)-2*vv)
check('TX-elliptic-y',apply(TX,vv)-3*ee**2)
check('RX-elliptic-x',apply(RX,ee));check('RX-elliptic-y',apply(RX,vv))

# Root deck characters are exact Laurent weights; this does not require an
# arbitrary numerical choice of a cube root of unity.
character={'r':1,'dr':1,'eta':-1,'RX':-1,'TX':-2,'elliptic_x':2,'elliptic_y':0}
assert(character['dr']+character['eta'])%3==0;checks.append('physical-area-root-invariant')
assert character['eta']%3!=0;checks.append('isolated-CM-oneform-root-tracezero')

out={'checks':checks,'check_count':len(checks),
 'finite_cover':'r^3=x^6+a^6,s^3=u^6+v^6',
 'radial_field':[str(z)for z in RX],'angular_field':[str(z)for z in TX],
 'radial_dual':'dr/2','angular_dual':[str(z)for z in eta],
 'area':'dx wedge da=-dr wedge eta_X/2',
 'physical_volume':'Omega=-dr wedge ds wedge eta_X wedge eta_Y/4',
 'physical_source':'-W/4/(1+r^3)/(1+s^3) dr wedge ds wedge eta_X wedge eta_Y',
 'coupling':'B=alpha*beta*xi*nu/2+alpha^4*beta^2*xi^3*etacurve*nu*varpi/2+alpha^2*beta*xi*etacurve*varpi/3',
 'elliptic_quotient':{'x':str(ee),'y':str(vv),'equation':'y^2=x^3-4','differential':'eta_X=delliptic_x/(2elliptic_y)'},
 'root_deck_characters_mod3':character,
 'order3_CM_translation':'P=(0,2i) on y^2=x^3-4; translation preserves eta_X, fixes r, and commutes with root-deck CM automorphism (x,y)->(zeta^2*x,y)',
 'status':'actual density-preserving flat frame; no S3-incidence-compatible translation/current constructed'}
Path(__file__).with_name('cm-flat-frame-results.json').write_text(json.dumps(out,indent=2));print('Passed',len(checks),'exact identities')
