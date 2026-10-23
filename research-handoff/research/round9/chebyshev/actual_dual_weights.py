from pathlib import Path
import json
P=Path(__file__).parent
# Generic leading valuations of s,a0,a1,b1,b2,r,h in each cover; f_s=6s5+(4a0/3)s3+b1s2+a1b2/9.
raw={'main_qinf_h0':(0,0,0,0,0,0,6),'next_RES':(3,0,3,3,6,0,9),'q0_h0':(3,0,3,3,6,0,3),'q0_r0':(5,10,10,15,15,5,0),'qinf_r0':(-5,-10,-6,-3,-15,3,0),'J0_hinf':(-14,-24,-27,-39,-42,-12,-6),'qinf_hinf':(-12,-12,-21,-27,-36,-6,-3),'q0_hinf':(-8,-12,-15,-21,-24,-6,-3)}
res={}
for name,(s,a0,a1,b1,b2,r,h)in raw.items():
 fs=min(5*s,a0+3*s,b1+2*s,a1+b2)
 g=[2*s+min(a0+s,b1,3*s),4*s,3*s,r+2*s,r+min(a1+s,b2),h+3*r+s]
 phi=[v-fs for v in g]
 res[name]={'parameter_valuations':dict(zip(['s','a0','a1','b1','b2','r','h'],raw[name])),'f_s':fs,'actual_trace_dual_valuations':phi}
assert res['next_RES']['actual_trace_dual_valuations']==[0,3,0,-3,-3,3]
assert res['q0_h0']['actual_trace_dual_valuations']==[0,3,0,-3,-3,-3]
out={'corners':res,'warning':'Generic leading valuations, before special-point cancellations; use explicit trace duals rather than inverse basis weights. The earlier RES shortage was false.','corrected_interpolation':'No q0h0 adjoint conditions; nextRES adds no stronger condition than mainE. The original73jet fullrankspace is conservative/sufficient for these generic valuations.'}
(P/'actual_dual_weights.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
