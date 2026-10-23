"""A polynomial pole-two frame with only actual discriminant denominators.

Includes all exact lower Jacobian decompositions, not just a cohomology gauge.
"""
from pathlib import Path
import sympy as s,pickle,json,time,importlib.util,re
from sympy.polys.matrices import DomainMatrix
root=Path(__file__).parent;start=time.monotonic()
spec=importlib.util.spec_from_file_location('native_rf',root/'theta_frame.py');rf=importlib.util.module_from_spec(spec);spec.loader.exec_module(rf)
RF,convert,zero,one=rf.RF,rf.convert,rf.zero,rf.one
raw=pickle.loads((root/'actual_fast.pickle').read_bytes());W,h,t,L,r,x=raw['symbols'];vv=(W,h,t);C=raw['curve']
input=pickle.loads((root/'global_eta_input.pickle').read_bytes());den=input['common_denominator'];nums=input['numerators'];mons=input['monomials']
text=(root/'global_eta_lift.log').read_text();cs=[]
for i in range(1,11):
    value=text.split('COEFFICIENT '+str(i)+'\n')[1].split('\n')[0]
    cs.append(s.sympify(value.replace('^','**'))/x)
cs=[s.cancel(z)for z in cs];assert all(s.denom(z).is_number for z in cs)
old=json.loads((root/'theta_frame.json').read_text())
D1,D2=[s.sympify(z['factor'].replace('^','**'))for z in old['old_denominator_factors'][:2]]
assert s.expand(sum(c*n for c,n in zip(cs,nums))-D1*D2)==0
newnum=s.expand(sum(c*m for c,m in zip(cs,mons)))
rows=[s.Poly(m,*vv).monoms()[0]for m in mons]
labs=raw['lab8'];mon=lambda e:W**e[0]*h**e[1]*t**e[2]
J=s.Matrix([[s.Poly(s.diff(C,vv[i])*mon(e),*vv).coeff_monomial(mm)for i,e in labs]for mm in mons])
B=J.row_join(s.Matrix([int(mm==t**4)for mm in mons]));DM=DomainMatrix.from_Matrix((x*B).applyfunc(s.expand));iv,de=DM.inv_den();iv=iv.to_Matrix();de=DM.domain.to_sympy(de)
T=[[convert(x*iv[i,j]/de)for j in range(10)]for i in range(10)]
cRF=[convert(c)for c in cs];etaold=[sum((T[i][j]*cRF[j]for j in range(10)),zero)for i in range(10)];ww=etaold[-1]
assert not(ww-convert(D1*D2/den)).n
Tnew=[[T[i][j]-etaold[i]*T[-1][j]/ww for j in range(10)]for i in range(9)]+[[T[-1][j]/ww for j in range(10)]]
div=s.Matrix([[s.Poly(s.diff(mon(e),vv[i]),*vv).coeff_monomial(z)for i,e in labs]for z in (h*h,t)])
holrow=[sum((convert(div[i,k])*etaold[k]for k in range(9)),zero)for i in range(2)]
P=[[one,zero,zero],[zero,one,zero],holrow+[ww]]
inv=[[one,zero,zero],[zero,one,zero],[-P[2][0]/ww,-P[2][1]/ww,one/ww]]
newbasis=B.copy();newbasis[:,-1]=s.Matrix([cs[j]for j in range(10)])
assert all(not(v-(one if i==j else zero)).n for i,row in enumerate(rf.mul([[convert(v)for v in row]for row in newbasis.tolist()],Tnew))for j,v in enumerate(row))
newN={};holprims={}
for name in ('L','r','x'):
    left=rf.add([[v.diff(name)for v in row]for row in P],rf.mul(P,rf.N[name]));newN[name]=rf.mul(left,inv)
    assert all(not(a-b).n for ar,br in zip(rf.mul(newN[name],P),left)for a,b in zip(ar,br))
    DC=s.diff(C,{'L':L,'r':r,'x':x}[name]);pr=[]
    for hol in (h*h,t):
        target=[convert(s.Poly(hol*DC,*vv).coeff_monomial(mm))for mm in mons]
        coeff=[sum((Tnew[i][j]*target[j]for j in range(10)),zero)for i in range(10)]
        hp=[-sum((convert(div[i,k])*coeff[k]for k in range(9)),zero)for i in range(2)]+[-coeff[-1]]
        assert all(not(a-b).n for a,b in zip(hp,newN[name][len(pr)]))
        pr.append(dict(Jacobian_coefficients=[v.json()for v in coeff[:9]],eta_coefficient=coeff[-1].json(),
                       connection_row=[v.json()for v in hp],primitive='i_Q Omega/C, Q_i=sum coefficients[k]*monomial(lab8[k]) in component lab8[k][0]'))
    holprims[name]=pr
def common_den(mat):
    d=rf.ctx.constant(1)
    for row in mat:
        for v in row:d=d*v.d//d.gcd(v.d)
    return [{'factor':str(f),'exponent':int(e)}for f,e in d.factor()[1]]
denfacts={k:common_den(mat)for k,mat in newN.items()}
lowerfacts=common_den(Tnew)
for facts in list(denfacts.values())+[lowerfacts]:
    for f in facts:
        ff=convert(s.sympify(f['factor'].replace('^','**')))
        allowed=[convert(z)for z in (x,D1,D2)]
        assert any(ff.n==g.n and ff.d==g.d for g in allowed),(f,allowed)
packet=dict(symbols=raw['symbols'],curve=C,basis=[h*h,t,newnum],basis_pole_orders=[1,1,2],new_numerator=newnum,
            numerator_coefficients=cs,monomials=mons,lab8=labs,
            P=[[z.json()for z in row]for row in P],connection={name:[[v.json()for v in row]for row in mat]for name,mat in newN.items()},
            lower_Jacobian_inverse=[[v.json()for v in row]for row in Tnew],hol_primitives=holprims,
            denominators=denfacts,lower_denominators=lowerfacts,common_numerator_witness=D1*D2,
            frame_convention='rows are basis derivatives; coefficient columns use transpose; eta_new is the literal polynomial pole-two form',
            exact_full_lower_decompositions=True,exact_cohomology_gauge=True,seconds=time.monotonic()-start)
(root/'global_eta_frame.pickle').write_bytes(pickle.dumps(packet))
js=dict(new_numerator=str(newnum),numerator_coefficients=[str(c)for c in cs],denominators=denfacts,lower_denominators=lowerfacts,
        exact_full_lower_decompositions=True,exact_cohomology_gauge=True,seconds=time.monotonic()-start,
        scope='Actual good frame and all holomorphic Q8 primitives; no primitive for the target source. Higher pole-three primitives are not reconstructed here.')
(root/'global_eta_frame.json').write_text(json.dumps(js,indent=2)+'\n');print(json.dumps(js,indent=2))
