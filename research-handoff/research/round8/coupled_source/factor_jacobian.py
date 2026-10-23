"""Native exact factorization of the physical-to-canonical base Jacobian."""
from pathlib import Path
import json,pickle,time
from flint import fmpq,fmpq_mpoly_ctx

HERE=Path(__file__).parent
start=time.monotonic()
ctx=fmpq_mpoly_ctx.get(('a','b','v'));a,b,v=ctx.gens();c=fmpq(5,7)
B=b*(1+a*v);P=1+v**6;Q=c*a*b*v;R=c*(a*b+v*b**3);S=1+a**6+b**6
A=3*S-B*R
H=27*P*S*S-9*Q*R*S+2*R**3
J=3*S*Q-R*R
gradient=lambda f:[f.derivative(i)for i in range(3)]
gA,gB,gH,gJ=map(gradient,[A,B,H,J])
Lvec=[A*gH[i]-2*H*gA[i]for i in range(3)]
Rvec=[B*A*gJ[i]-J*(A*gB[i]+B*gA[i])for i in range(3)]
Xvec=[3*A*gB[i]-B*gA[i]for i in range(3)]
K=sum((-1 if (i,j,k)in [(0,2,1),(1,0,2),(2,1,0)]else 1)*Lvec[i]*Rvec[j]*Xvec[k]
      for i,j,k in [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)])
constant,factors=K.factor()
reconstructed=ctx.constant(constant)
for f,m in factors:reconstructed*=f**m
assert reconstructed==K
Delta=next(f for f,m in factors if len(f.to_dict())==47)
E=1+a*v
assert K==fmpq(1215,343)*b*b*E*S*S*A*A*Delta
report={'jacobian':'K/A^7','A':'3*S-B*R','L':'H/(3*A^2)','r':'J/(B*A)','x':'3*B^3/A',
        'K_terms':len(K.to_dict()),'constant':str(constant),
        'factors':[{'factor':str(f),'multiplicity':m,'terms':len(f.to_dict())}for f,m in factors],
        'seconds':round(time.monotonic()-start,3)}
(HERE/'jacobian_factorization.json').write_text(json.dumps(report,indent=2)+'\n')
polys=[('A',A),('B',B),('E',E),('H',H),('J',J),('S',S),('R',R),('K',K),('Delta47',Delta)]
(HERE/'jacobian_native.pickle').write_bytes(pickle.dumps({name:{e:str(x)for e,x in f.to_dict().items()}for name,f in polys}))
cross=lambda U,V:[U[(i+1)%3]*V[(i+2)%3]-U[(i+2)%3]*V[(i+1)%3]for i in range(3)]
crossRX,crossXL,crossLR=cross(Rvec,Xvec),cross(Xvec,Lvec),cross(Lvec,Rvec)
common=fmpq(1215,343)*b*b*E*S*S*Delta
raw_fields={'L':[(3*A*f,common)for f in crossRX],
            'r':[(B*B*f,common)for f in crossXL],
            'x':[(f,3*B*B*common)for f in crossLR]}
field_pairs={}
for name,pairs in raw_fields.items():
    field_pairs[name]=[]
    for num,den in pairs:
        gcd=num.gcd(den);num//=gcd;den//=gcd
        field_pairs[name].append({'numerator':{e:str(x)for e,x in num.to_dict().items()},
                                  'denominator':{e:str(x)for e,x in den.to_dict().items()}})
(HERE/'coordinate_fields.pickle').write_bytes(pickle.dumps({'variables':('a','b','v'),'fields':field_pairs,'polynomials':{name:{e:str(x)for e,x in f.to_dict().items()}for name,f in polys}}))
print(json.dumps(report,indent=2))
