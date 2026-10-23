"""Compact exact coordinate-lift circuit for the actual quartic source.

The inverse four-by-four matrix is retained as a circuit, not expanded.
The accompanying README derives the exact identities from its defining
linear equation.  A good finite fiber proves its determinant is nonzero.
"""
import os
os.environ["EIGHT_MODEL"]="quartic"
import current_search as m
import pickle,json
from flint import nmod_poly,nmod_mat

p=m.prime
point=(1,2,3,5)
data=m.evaluate(point)
gs=data[3]['g']; grad=data[3]['derivatives']
G=nmod_poly(gs,p);z=nmod_poly([0,1],p)
N=nmod_poly([-1,0,3,0,-3,0,1],p)
c0=-pow(gs[0],-1,p)%p
c2=pow(5*gs[4]%p,-1,p)
w=nmod_poly([c0,0,c2],p)
Fz=G+z*G.derivative()
numer=N-w*Fz
assert int(numer[0])==0 and numer.degree()<=5
R=nmod_poly([int(numer[k+1]) for k in range(5)],p)
bar=R%G
mat=nmod_mat([[(grad[i][k]-gs[k]*grad[i][4]*pow(gs[4],-1,p))%p
                for i in range(4)] for k in range(4)],p)
assert int(mat.det())
v=mat.solve(nmod_mat([[int(bar[k])] for k in range(4)],p))
vv=[int(v[k,0]) for k in range(4)]
Q=(-4*c2*gs[3]-sum(vv[i]*grad[i][4] for i in range(4)))*pow(gs[4],-1,p)%p
identity=N-w*Fz-z*sum((vv[i]*nmod_poly(grad[i],p) for i in range(4)),nmod_poly([],p))-Q*z*G
assert identity.is_zero()
report=dict(prime=p,point=point,quartic_coefficients=gs,
            determinant=int(mat.det()),v=vv,Q=Q,
            exact_matrix='M[k,i]=partial_i g[k] - g[k]*partial_i g[4]/g[4], k=0..3',
            exact_c0='-1/g0',exact_c2='1/(5*g4)',
            exact_rhs='rem_z(((z^2-1)^3-(c0+c2*z^2)*(G+z*Gprime))/z,G)',
            exact_lift='v=M^-1 rhs; Q=(-4*c2*g3-sum(v_i*partial_i g4))/g4',
            exact_normal_identity='(z^2-1)^3=(c0+c2*z^2)*(G+z*Gprime)+z*sum(v_i*partial_i G)+Q*z*G',
            exact_source_identity='rho=(2*c0+(div(v)+Q)*z+4*c2*z^2)/Gprime-sum(D_i(v_i*z/Gprime))',
            source_factor='-1/512',
            scope='Exact rational coordinate-lift circuit, with a residual scalar coefficient; not a primitive or certificate.')
(m.HERE/'normal_lift.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
