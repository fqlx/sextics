"""Independent Taylor-jet audit of off_paired's pencil-normal cone frame."""
from pathlib import Path
import pickle,json
from physical import J1,J2,Poly,dot
root=Path(__file__).parent;hold=json.loads(Path('/workspace/research/round10/cone_radial/frame_holdouts.json').read_text());raw=pickle.loads(Path('/workspace/research/round10/cone_radial/frame.pickle').read_bytes())
def point(pt,p):
    J1.p=J2.p=p;args=[J2(v,seed=i)for i,v in enumerate(pt)];vals=[Poly(raw[k],p).eval(args)for k in ('N0p','N1p')];F,G=[v.first()for v in vals]
    df,dg=[[v.derivative(i)for i in range(3)]for v in vals];jac=df[0]*dg[1]-df[1]*dg[0]
    VF=[dg[1]/jac,-dg[0]/jac,J1()];VG=[-df[1]/jac,df[0]/jac,J1()]
    Vq=[(df[1]*dg[2]-df[2]*dg[1])/jac,(df[2]*dg[0]-df[0]*dg[2])/jac,J1(1)];dual=[VF,VG,Vq]
    for i,grad in enumerate([df,dg,[J1(),J1(),J1(1)]]):
        for j,V in enumerate(dual):
            z=dot(grad,V);assert z.v==int(i==j) and not any(z.g)
    for i in range(3):
        for j in range(i+1,3):
            bracket=[sum(dual[i][k].v*dual[j][ell].g[k]-dual[j][k].v*dual[i][ell].g[k]for k in range(3))%p for ell in range(3)]
            assert not any(bracket)
    E=[F*VF[i]+G*VG[i]for i in range(3)];fields=dict(dual_N0=VF,dual_N1=VG,dual_v=Vq,Euler=E)
    if F.v:
        radial=[v/(F*F)for v in E];fields['radial']=radial;fields['curve_s']=[F*v for v in VG]
        div=sum(v.g[i]for i,v in enumerate(radial))%p
        assert (div+sum(v.v*jac.g[i]*pow(jac.v,-1,p)for i,v in enumerate(radial)))%p==0
    return F,G,jac,fields
checks=[]
for rec in hold['holdouts']:
    F,G,jac,fields=point(rec['pt'],hold['prime'])
    for z,key in [(F,'N0p'),(G,'N1p'),(jac,'Jab')]:assert z.v==rec[key]['value'] and list(z.g)==rec[key]['gradient']
    for name,V in fields.items():
        for z,expected in zip(V,rec['fields'][name]):assert z.v==expected['value'] and list(z.g)==expected['gradient']
    checks.append(dict(point=rec['pt'],all_values_gradients=True,dual_first_jet_identity=True,dual_fields_commute=True,radial_divergence_identity=True))
cone=hold['cone_good_point'];F,G,jac,fields=point(cone['point'],cone['prime']);assert F.v==G.v==0 and jac.v==48
ans=dict(independent_Taylor_jets=True,records=checks,cone_Jab=jac.v,cone_normalization='Uses exactly canceled canonical Teff numerator/denominator from the saved source packet.',
         radial_identity='div(E/N0²)=−(E/N0²)(log Jab)',
         physical_density_identity='div(radial)+radial(log(rho*fT))=radial(log(rho*fT/Jab))',
         passed=True,scope='Frame and derivative audit only, no source primitive or cone extension claim.')
(root/'radial_audit.json').write_text(json.dumps(ans,indent=2)+'\n');print(json.dumps(ans,indent=2))
