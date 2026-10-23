"""Actual q-character genus4 cover: moving CM quotient maps and cochains.

This retains the finite q deck and every fixed-C normal.  The two new CM
channels complement the prior two varying elliptic channels; no weighted
source is replaced by an unweighted holomorphic tensor.
"""
from pathlib import Path
import sympy as s,json
u,w,q,J,z,lam=s.symbols('u w q J z lam',nonzero=True)
alpha=3*z*z/4;d=1+z**6-J
etaB=2*u+w**3-alpha
E=2*u-2*w**3-alpha-9*z*q*w*w
relations=[q*q-u*w,u*u+(w**3-alpha)*u+d,lam**6-d]
G=s.groebner(relations,q,u,lam,domain=s.QQ.frac_field(w,J,z))
def red(v):
    num=s.cancel(v).as_numer_denom()[0]
    return s.factor(G.reduce(num)[1])
checks={}
def ck(name,v):
    checks[name]=red(v)==0
    assert checks[name],(name,red(v))
def N(v):
    return s.diff(v,J)+s.diff(v,u)/E-(w+3*z*q)*s.diff(v,w)/(u*E)-3*z*s.diff(v,q)/(2*E)-s.diff(v,lam)/(6*lam**5)
U=u/lam**3;W=w/lam;Q=q/lam**2;a=alpha/lam**3
eta=U-1/U
Tp=Q*(1+1/U);Tm=Q*(1-1/U)
bp=a+2;bm=a-2
ck('actual_normalized_genus4_cubic',U*U+(W**3-a)*U+1)
ck('actual_normalized_genus4_q_character',Q*Q-U*W)
ck('actual_eta',etaB/lam**3-eta)
ck('actual_plus_CM_quartic',Tp*Tp+W**4-bp*W)
ck('actual_minus_CM_quartic',Tm*Tm+W**4-bm*W)
ck('FULL_lambda_normal',N(lam)+lam/(6*d))
ck('FULL_a_normal',N(a)-a/(2*d))
ck('FULL_U_normal',N(U)-1/(lam**3*E)-U/(2*d))
ck('FULL_W_normal',N(W)+(w+3*z*q)/(u*lam*E)-W/(6*d))
ck('FULL_Q_normal',N(Q)+3*z/(2*lam**2*E)-Q/(3*d))
ck('FULL_plus_CM_normal',N(Tp*Tp+W**4-bp*W))
ck('FULL_minus_CM_normal',N(Tm*Tm+W**4-bm*W))
ck('actual_odd_hol0_quotient_differential',1/(Q*eta)-(1/Tm-1/Tp)/2)
ck('actual_odd_hol1_quotient_differential',U/(Q*eta)-(1/Tm+1/Tp)/2)
# The two involutions are literal on the original normalized genus4 curve.
for name,sg in [('tauplus',1),('tauminus',-1)]:
    Ui=1/U;Qi=sg*Q/U
    ck(name+'_preserves_curve',Ui*Ui+(W**3-a)*Ui+1)
    ck(name+'_preserves_q_character',Qi*Qi-Ui*W)
    ck(name+'_is_involution',sg*Qi/Ui-Q)
# Constant-j0 normalization and its compulsory moving-parameter cochain.
WW,TT,cc,bb=s.symbols('WW TT cc bb',nonzero=True)
x=cc/WW;y=TT/WW**2
for name,expr in [('dW',s.diff(x,WW)/y+cc/TT),
                  ('dc',s.diff(x,cc)/y-WW/TT)]:
    checks['absolute_constant_CM_'+name]=s.factor(expr)==0
    assert checks['absolute_constant_CM_'+name]
out={
 'status':'PASS_ACTUAL_FOUR_ELLIPTIC_CHANNELS_WITH_Q_DECK_AND_FULL_MOVING_NORMALS; WEIGHTED_CONTRACTION_OPEN',
 'checks':checks,'check_count':len(checks),
 'actual_genus4':'u²+(w³−alpha)u+d=0,q²=u*w,alpha=3z²/4,d=1+z6−J.',
 'actual_scale':'lambda6=d,U=u/lambda3,W=w/lambda,Q=q/lambda2,a=alpha/lambda3,eta=U−1/U.',
 'two_involutions':'tau±(U,W,Q)=(1/U,W,±Q/U), each fixes a and preserves both actual equations. Their product is the actual q deck.',
 'new_CM_quotients':'Tplus=Q(1+1/U),Tminus=Q(1−1/U); T±²=−W4+(a±2)W. Both quotient elliptic curves have j=0.',
 'two_odd_holomorphic_channels':'omega_o0=dW/(Q*eta)=(dW/Tminus−dW/Tplus)/2; omega_o1=U*dW/(Q*eta)=(dW/Tminus+dW/Tplus)/2.',
 'constant_CM_maps':'Choose c±³=b±=a±2. x±=c±/W,y±=T±/W² satisfy y±²=x±³−1. FULL dx±/y±=−c±*dW/T±+W*dc±/T±, dc±=da/(3c±²).',
 'absolute_moving_CM_cochain':'dW/T±=−c±^-1*omega_CM±+W*da/[3b± T±]. The da term cannot be discarded in a primitive; it vanishes only against the actual dJ wedge dz source-base pair.',
 'FULL_fixed_C_normal':{'Nlambda':'−lambda/(6d)','Na':'a/(2d)','NU':'1/(lambda3 E)+U/(2d)',
   'NW':'−(w+3zq)/(u lambda E)+W/(6d)','NQ':'−3z/(2lambda2 E)+Q/(3d)',
   'NTplus':'NQ*(1+1/U)−Q*NU/U²','NTminus':'NQ*(1−1/U)+Q*NU/U²','Ncplus':'Na/(3cplus²)','Ncminus':'Na/(3cminus²)'},
 'source_binding':'Use the actual whole current and nonzero weighted packet from actual_new_companion_phiH_whole_prefix.json. Its weight NlogPhi depends on q and E, so the two prior q-even channels alone do not carry the entire correction. No unweighted trace or CM-tensor exactness is asserted.',
 'coupling_warning':'Although its q-odd differential may reduce relatively, a fiber primitive multiplies thetaP(H,C,p). Its full exterior derivative includes dC and endpoint coefficient normals. Those are required in the eventual contraction.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checks),'actual genus4 CM quotient maps and all moving fixed-C normals')
