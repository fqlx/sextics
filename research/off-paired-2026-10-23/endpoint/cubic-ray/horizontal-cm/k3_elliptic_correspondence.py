"""Exact source-retaining K3/two-fixed-elliptics finite correspondence.

The correspondence simplifies the geometry, but does not integrate the
actual coefficient R, H or B. No primitive is asserted.
"""
import json
from pathlib import Path
import sympy as S

c,h,T,e,w,Y,V=S.symbols('c h T e w Y V',nonzero=True)
coordinates=[c,h,T,e]
relations=[w**3-1-T**6,Y**2-1+e**3,w*V**2-e]
domain=S.QQ.frac_field(c,h,T,e)
GB=S.groebner(relations,V,Y,w,domain=domain)
checks=[]
def reduce(value):
    numerator,denominator=S.fraction(S.cancel(value))
    remainder=GB.reduce(numerator)[1]
    return S.cancel(remainder/denominator)
def check(name,value):
    result=reduce(value)
    assert result==0,(name,S.factor(result))
    checks.append(name)
def derivative(value,q):
    result=S.diff(value,q)
    if q==T:
        result+=S.diff(value,w)*2*T**5/w**2
        result-=S.diff(value,V)*V*T**5/w**3
    if q==e:
        result-=S.diff(value,Y)*3*e**2/(2*Y)
        result+=S.diff(value,V)*V/(2*e)
    return S.cancel(result)

U=T*V
Z=c**3*Y
u=c*U
v=c*V
check('normalized-K3',Y**2+U**6+V**6-1)
H=1+Z**(-2)+h**6
C=Z**2+u**6+v**6
B=u/2+h*v/3+h*u*v/(2*Z)
check('C-normalization',C-c**6)
check('H-full-source-coefficient',H-(1+c**(-6)*Y**(-2)+h**6))
check('B-full-source-coefficient',B-(c*V*(T/2+h/3)+h*T*V**2/(2*c*Y)))

E1=w**2/T**2
Y1=(T**6-1)/T**3
check('first-fixed-elliptic',Y1**2-E1**3+4)
check('first-elliptic-differential',derivative(E1,T)/(2*Y1)-1/w)
check('second-fixed-elliptic',Y**2-1+e**3)
check('finite-inverse-b-square',(w/T)**2-E1)
check('finite-inverse-T-cube',T**3-(Y1+(w/T)**3)/2)

# Relative K3 two-form, with C fixed:
# dU dV/Y = dT de/(2wY) = (dE1/2Y1)(de/2Y).
angle_jac=derivative(U,T)*derivative(V,e)-derivative(U,e)*derivative(V,T)
check('K3-two-form-product',angle_jac/Y-1/(2*w*Y))

# The four-form is the actual -dZ dh du dv/3 from the rational chart.
original=[Z,h,u,v]
Jac=S.Matrix([[derivative(value,q) for q in coordinates]for value in original])
physical_volume=-Jac.det()/3
check('actual-four-form-product',physical_volume+c**4/(2*w*Y))
check('canonical-source-normalization',c**4/c**6-c**(-2))

# Explicit character checks prevent an isolated CM factor being traced to
# zero accidentally. The complete physical product has character zero.
root_characters={
 'c_root_mod6':{'c':1,'Y':-3,'V':-1,'T':0,'w':0,'e':-2,
                 'eta1':0,'eta2':1,'density_total':4+1+0+1},
 'w_root_mod3':{'c':0,'Y':0,'V':0,'T':0,'w':1,'e':1,
                 'eta1':-1,'eta2':1,'density_total':0-1+1},
}
for name,character in root_characters.items():
    modulus=6 if name.endswith('6') else 3
    assert character['density_total']%modulus==0
    checks.append(name+'-physical-density')
    assert (-6*character['c']-2*character['Y'])%modulus==0
    checks.append(name+'-H')
    assert (character['c']+character['V'])%modulus==0
    assert (2*character['V']-character['c']-character['Y'])%modulus==0
    checks.append(name+'-full-B')

data={
 'status':'Explicit finite source-retaining correspondence; no primitive or certificate',
 'constant_scope':'fixed k characteristic zero; k=C for full complex contract',
 'check_count':len(checks),'checks':checks,
 'finite_field_relations':['w^3=1+T^6','Y^2=1-e^3','V^2=e/w'],
 'map_to_physical_chart':{'Z':'c^3*Y','h':'h','u':'c*T*V','v':'c*V'},
 'normalized_K3':'Y^2+(T*V)^6+V^6=1',
 'elliptic_1':{'e1':'w^2/T^2','y1':'(T^6-1)/T^3',
               'equation':'y1^2=e1^3-4','differential':'eta1=de1/(2*y1)=dT/w'},
 'elliptic_2':{'equation':'Y^2=1-e^3','differential':'eta2=de/(2*Y)'},
 'finite_map_bounds':{'to_normalized_K3':'degree at most 3 (adjoin w)',
   'to_elliptic_product':'degree at most 12: b^2=e1,T^3=(y1+b^3)/2,w=b*T,V^2=e/w'},
 'K3_differential':'dU ^ dV/Y=eta1 ^ eta2',
 'physical_volume':'-c^4 dc ^ dh ^ eta1 ^ eta2',
 'coefficients':{'C':'c^6','H':'1+c^-6*Y^-2+h^6',
                 'B':'c*V*(T/2+h/3)+h*T*V^2/(2*c*Y)'},
 'root_characters':root_characters,
 'actual_source':'-c^4*R dc ^ dh ^ eta1 ^ eta2 = -W/(c^2*H) dc ^ dh ^ eta1 ^ eta2',
 'warning':'H and full B vary along the elliptic product; no source primitive follows from density factorization',
}
Path(__file__).with_name('k3-elliptic-correspondence-results.json').write_text(json.dumps(data,indent=2)+'\n')
print('Passed',len(checks),'exact field, differential and full-source checks')
