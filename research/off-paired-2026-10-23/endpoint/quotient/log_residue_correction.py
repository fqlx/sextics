"""Actual nonexact conic-log residue classes plus compact same-pole corrections.

For s=-3z/2,L=H+sC,T²=L²-4s6,r=(L+T)/(2s³), normalizedthirdkind
current τ_s dlogr wedge dlogg is rational aftertrace. Its compactsource
is d_g*MHe0, with d_g=V(C)-2C V(s)/s, V=(gradL-3L grads/s)cross gradlogg.
The explicit verticalexactcorrection is supplied in jacobianagent's audit.
No degreeextensions: append g=x,y,z to prior compactFs correctionspace.
"""
import physical_discriminant_correction as base
import numpy as np,json,time,argparse
from pathlib import Path
root=Path(__file__).parent

def log_scalars(points,p):
 u,v,z=points.T
 inv=lambda arr:np.array([pow(int(a),-1,p)for a in arr],dtype=np.int64)
 power=lambda arr,n:np.array([pow(int(a),n,p)for a in arr],dtype=np.int64)
 ui,vi,zi=inv(u),inv(v),inv(z);iv2=pow(2,-1,p);iv3=pow(3,-1,p)
 h=(1+power(u,6)*vi%p*vi+v*v+power(z,6)+u*z*iv2)%p;c=(power(u,3)*z%p*vi%p*iv2+u*iv3)%p;s=-3*z*iv2%p;L=(h+s*c)%p
 lu=(6*power(u,5)*vi%p*vi-9*power(u,2)*z%p*z%p*vi%p*pow(4,-1,p))%p
 lv=(-2*power(u,6)*vi%p*vi%p*vi+2*v+3*power(u,3)*z%p*z%p*vi%p*vi%p*pow(4,-1,p))%p
 lz=(6*power(z,5)-3*power(u,3)*z%p*vi%p*iv2)%p
 B=np.stack([lu,lv,(lz-3*L*zi)%p],axis=1)
 cu=(3*power(u,2)*z%p*vi%p*iv2+iv3)%p;cv=-power(u,3)*z%p*vi%p*vi%p*iv2%p;cz=power(u,3)*vi%p*iv2%p
 dc=np.stack([cu,cv,cz],axis=1);zero=np.zeros(len(u),dtype=np.int64)
 gradlog=[np.stack([ui,-vi*iv3%p,zero],axis=1),np.stack([zero,vi*iv3%p,zero],axis=1),np.stack([zero,zero,zi],axis=1)]
 out=[]
 for gg in gradlog:
  V=np.cross(B,gg)%p;VC=np.sum(V*dc,axis=1)%p
  out.append((VC-2*c*V[:,2]%p*zi)%p)
 return out

def matrix_for(labels,points,p):
 mat,rhs=base.matrix_for(labels,points,p,1);bi,source=base.q.connection(points,p);fs=base.eval_fs(points,p,1)
 cols=[]
 for scalar in log_scalars(points,p):cols.append((-18*source[base.rows]*scalar%p*fs).T.reshape(-1)%p)
 return np.column_stack([mat]+cols),rhs

def run(k,p):
 labels=base.labels_for(k);points=base.q.sample_points(len(labels)+15,p,718294+k);mat,rhs=matrix_for(labels,points,p)
 start=time.monotonic();rank,sol=base.q.old.solve_mod(mat,rhs,p)
 out={'pole':1,'compact_extra_X0_degree':k,'log_classes':['x','y','z'],'prime':p,'unknowns':mat.shape[1],'rows':len(rhs),'rank':rank,'consistent_evaluations':sol is not None,'solve_seconds':time.monotonic()-start}
 if sol is not None:
  fresh=base.q.sample_points(400,p,813471+k);fm,fr=matrix_for(labels,fresh,p);out['fresh_nonzero_residuals']=int(np.count_nonzero((fm@sol-fr)%p));out['candidate_coefficients']=[int(a)for a in sol]
 print(json.dumps({a:b for a,b in out.items()if a!='candidate_coefficients'}),flush=True);return out
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--k',nargs='+',type=int,default=[0,1]);parser.add_argument('--prime',type=int,default=1009);args=parser.parse_args();out=[]
 for k in args.k:
  out.append(run(k,args.prime));(root/'log-residue-correction-results.json').write_text(json.dumps(out,indent=2))
