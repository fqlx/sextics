from pathlib import Path
import sympy as S,pickle
P=Path(__file__).parent;d=pickle.loads((P/'blowup_qinf_h0.pickle').read_bytes());Q,H=d['Q'],d['H'];s,u,v,z=S.symbols('s u v z');a1,a0,b2,b1,b0=[d['coefficients'][k]for k in('a1','a0','b2','b1','b0')];al=S.cancel(a1/H);be=S.cancel(b1/H);ga=S.cancel(b2/H)
rels=[s*u-b2,u*u-H*v,s*v-ga*u,v*v+al*u*v+3*be*ga*u+3*a0*ga*ga+9*ga*ga*s*s,H*v+a1*u+3*b1*s+3*a0*s*s+9*s**4,u*v+a1*v+3*H*be*ga+3*a0*ga*s+9*ga*s**3]
# only first Q jets required to evaluate Q0 Jacobian.
rr=[S.expand(e.subs(Q,0)+Q*S.diff(e,Q).subs(Q,0))for e in rels]
def expr(f):
 p=S.Poly(f,Q,H,s,u,v);return '+'.join('('+str(c)+')*'+'*'.join(f'{x}^{e}'for x,e in zip((Q,H,s,u,v),ex)if e)if any(ex)else '('+str(c)+')'for ex,c in p.terms())
text='LIB "primdec.lib";\nring R=0,(z,Q,H,s,u,v),dp;\nideal I='+','.join(expr(e)for e in rr)+';\nideal J=I+minor(jacob(I),3)+ideal(Q);\nprint("SINGULAR ALONG Q0 OFF H0");ideal A=J+ideal(z*H-1);std(A);\nprint("SINGULAR ALONG Q0H0");ideal B=J+ideal(H);std(B);\nquit;\n';(P/'chart_singularity_slice.sing').write_text(text)
