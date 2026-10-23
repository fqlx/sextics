# Global toric geometry of the quartic support D4

This audits the proposed support \(D_4:X_1^2X_2Y_2+X_0^3Y_0=0\).
It does not construct a certificate. The local exceptional surfaces of a
naive bundle model do not alone compute the global H20; a different toric
compactification gives that global group directly.

## A birational torus model

The binomial ambient hypersurface is parametrized birationally by
\[
 X_0=r\lambda,\ X_1=s\lambda,\ X_2=t\lambda,\quad
 Y_0=-s^2t\mu,\ Y_2=r^3\mu,\ Y_1=v.
\]
On the dense torus chart \(s=\mu=1\), the intersection with the target
sextic is exactly
\[
 F_4=v^6+\lambda^6+r^6\lambda^6+t^6\lambda^6+t^6+r^{18}
       -r^5t^2\lambda^4/3.
\]
The two terms linear in \(v\) cancel. Its Newton polytope is a
four-dimensional pyramid with apex \(v^6\). Its base in exponent
coordinates \((r,t,\lambda)\) has five vertices
\[
 (0,0,6),(6,0,6),(0,6,6),(0,6,0),(18,0,0).
\]
The sixth exponent \((5,2,4)\) is strictly interior to this base. Every
proper base face is a simplex with affinely independent monomials, hence
has a nondegenerate face polynomial. Every face containing the apex has
a unique nonzero \(v\)-derivative. It remains to check only the full
three-dimensional base polynomial.

## Exact nondegeneracy of the base face

Write \(R=r^6,T=t^6,L=\lambda^6\), and define the nonzero monomial
values
\[
 A=L,\ B=RL,\ C=TL,\ D=T,\ E=R^3,\ M=r^5t^2\lambda^4/3.
\]
The base polynomial and its three logarithmic derivatives would vanish
only if, for \(w=C/M\),
\[
 A=M(2w-1/6),\ B=M(-3w+5/6),\ D=M(1/3-w),\ E=C=Mw.
\]
Put \(a=2w-1/6,b=-3w+5/6,d=1/3-w\). The exact toric monomial relations
\(AD=C\), \(B^3=A^3E\), and \(729AM^6=B^5D^2\) imply
\[
 b^3d=a^2w^2,\qquad b^5d^2=729a.
\]
After clearing constants these are the polynomials
\[
 P=14904w^4-19980w^3+8892w^2-1725w+125,
\]
\[
 Q=-17006112w^7+34957008w^6-30757968w^5+15017400w^4
   -4394250w^3+770625w^2-102111672w+8506181.
\]
Their rational polynomial gcd is one. Thus there is no torus critical
point on the full base face. All faces of the full polytope are now
checked, so the Laurent hypersurface is nondegenerate.

## The global H20 conclusion

Choose a smooth projective toric refinement of the normal fan of this
integral polytope. The nondegenerate hypersurface has a smooth closure
\(Z_4\) there. Its divisor class \(D\) is nef and big, since the Newton
polytope has dimension four. It is birational to the original proposed
support.

On this smooth toric fourfold \(T\),
\(H^i(T,\mathcal O_T)=0\) for \(i>0\). The exact sequence for
\(Z_4\), Serre duality, and Kawamata--Viehweg vanishing give
\[
 H^2(Z_4,\mathcal O_{Z_4})
 \simeq H^3(T,\mathcal O_T(-D))
 \simeq H^1(T,K_T+D)^*=0.
\]
Thus a smooth projective resolution of this support has H20 zero.
The Brieskorn-type exceptional surfaces appearing in a different naive
model have local geometric genus, but their two-forms do not extend as
global holomorphic two-forms on the resolved threefold.

This conclusion uses standard toric nondegeneracy and vanishing theorems;
the checker verifies the explicit source substitution, face combinatorics,
and polynomial critical-point calculation. It is not Lean verification or
a solution of the original source problem.

Prepared with OpenAI Codex assistance.
