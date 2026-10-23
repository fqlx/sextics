# A normal rank-four model of the source-constant quotient

This note keeps the exact original source. It is a constructive model, not a certificate.

Use the affine coordinates \(x=X_1,y=Y_0,z=Y_1,a=X_2,b=Y_2\), and set

\[
 u=xy,\quad v=y^3,\quad w=x^3,\quad p=ab,
\]

\[
 e=zp/2,\quad f=z/2+p/3,\quad g=1+z^6+a^6+b^6,
 \quad S=g+fu.
\]

Then

\[
 vw=u^3,\qquad F=v^2+w^2+ew+S.
\]

The exact physical five-form is

\[
 \frac{y^3dx\,dy\,dz\,da\,db}{F^2}
 =\frac{du\,dv\,dz\,da\,db}{3F^2}
 =\frac{v^4du\,dv\,dz\,da\,db}{3G^2},
\]

where

\[
 G=v^4+Sv^2+eu^3v+u^6=v^2F.
\]

The quartic hypersurface \(G=0\) is nonnormal along \(u=v=0\).
The complete-intersection presentation \(vw=u^3,F=0\) retains the missing
\(w\)-coordinate and separates the two branches at that boundary. Over the
base \((u,z,a,b)\), it is a generically étale finite rank-four algebra with
integral basis

\[
 (1,v,w,v^2).
\]

Its multiplication rules include

\[
 vw=u^3,\quad w^2=-v^2-ew-S,\quad
 v^3=-Sv-u^3w-eu^3,\quad wv^2=u^3v.
\]

The discriminant of this basis is

\[
 \Delta_N=256u^{12}+(-128S^2+144Se^2-27e^4)u^6
                  +16S^4-4S^3e^2.
\]

Indeed \(\operatorname{disc}_vG=u^6\Delta_N\); the factor \(u^6\)
comes from the nonnormal quartic order. Generically at \(u=0\), the normal
model has two points with \(v=0,w^2+ew+S=0\) and two points with
\(w=0,v^2+S=0\), all distinct when \(S(4S-e^2)\ne0\).

## Actual second-pole source after normalization

Write

\[
 J_0=4v^2+ew+2S,\qquad J_2=2v^2-2w^2-ew=J_0-2F.
\]

The exact normal derivation on the toric surface \(vw=u^3\) is

\[
 \delta_F=\frac v{J_2}\partial_v-\frac w{J_2}\partial_w,
 \quad\delta_F(F)=1,\quad\delta_F(vw-u^3)=0.
\]

One must retain \(J_2\), rather than replace it by \(J_0\), before taking
normal derivatives. On \(F=0\), \(G_v=vJ_0\). The ordinary residue of
\(v^4dv/(3G^2)\) at a simple quartic root is

\[
 r=\frac{v(4v^2+4ew+6S)}{3J_0^3}.
\]

Thus the residue source is represented in the normal rank-four algebra
without an artificial \(u\)-pole. Its sign as a base four-form depends on
whether the normal differential is ordered before or after the base
volume. This is the same residue computed from the toric normal derivation
and the canonical two-form \(du\wedge dv/v\), with source multiplier
\(v/3\). The equality checks the second normal jet and the clearing factor
\(v^4\); it does not supply an exact primitive for \(r\).

## A source-carrying finite quartic correspondence

Ferrari factorization over a finite extension gives

\[
 G=(v^2+qv+r_0)(v^2-qv+s_0),
\]

\[
 m=q^2,\quad r_0+s_0=S+m,\quad q(s_0-r_0)=eu^3,
 \quad r_0s_0=u^6.
\]

Its cubic resolvent is

\[
 m^3+2Sm^2+(S^2-4u^6)m-e^2u^6=0,
\]

or \(m(m+S)^2=u^6(4m+e^2)\). Adjoin \(k^2=4q^2+e^2\) and use the
conic parameter

\[
 q=e(t-t^{-1})/4,\qquad k=e(t+t^{-1})/2.
\]

One obtains

\[
 u^3=(q/k)(g+fu+q^2).
\]

This leads to a depressed cubic in \(u\), followed by quadratic factors
for \(v\). The source remains the untraced rational expression \(r\)
in these variables. Tracing away the quartic roots loses its trace-zero
component; weighted traces require their derivative corrections.

Homogenizing \(u\) with weight two and \((X_0,z,a,b)\) with weight one,
the displayed cubic has degree six and weight sum six. Its generic
projective fibers over \(t\) are of Calabi–Yau-threefold type, rather than
an automatically serving Fano family. A finite correspondence alone does
not prove exactness of the physical source.

Prepared with OpenAI Codex assistance.
