# Independent audit of the coupled Euler current

The constructive conditional identity is correct, including the actual
physical density and both cubic components. No required pure-component
condition is concealed. The remaining field \(D\) has not been constructed,
so no primitive or certificate follows yet.

In the verified constant-density chart,

\[
H=1+Z^{-2}+h^6,\quad C=Z^2+u^6+v^6,\quad
B=u/2+hv/3+huv/(2Z),\quad \Omega=-dZ\wedge dh\wedge du\wedge dv/3.
\]

The actual source is \(R\Omega\), with
\(R=W/(HC)=Bp/(B+3Cp^2)^3\). Thus all vector-field divergences are ordinary
coordinate divergences, and the constant factor \(-1/3\) cancels from the
equation \(d\iota_J\Omega=R\Omega\).

Put

\[
E=h\partial_h-v\partial_v,\quad
K=2Ch^6-Hv^6,\quad
L=2(Z^2+u^6)h^6+(1+Z^{-2})v^6,\quad U=E/(12K).
\]

Direct exact differentiation gives

\[
\operatorname{div}E=0,\quad E(B)=0,\quad E(K)=6L,
\quad E(\log\kappa)=-\frac{6K}{HC},
\]
\[
U(\log\kappa)=-\frac1{2HC},\qquad
\operatorname{div}U=-\frac L{2K^2},\qquad
\kappa=B^3/(CH^2).
\]

The last divergence includes differentiating the full \(K\); it is not
zero. Since \(dV=-2W\,d\log\kappa\), the complete first current is

\[
\operatorname{div}(VU)=R-\frac L{2K^2}V.
\]

Let \(t_0=4\kappa+27\), and define

\[
f=\frac{27-2\kappa}{2t_0},\quad
c_0=\frac{3(27-23\kappa)}{t_0^2},\quad P=fV+W.
\]

The independent connection calculation gives
\(\theta f=-81\kappa/t_0^2\), so
\(\theta f+3/t_0=c_0\) and
\(-2f+(27-2\kappa)/t_0=0\). Hence

\[
dP=c_0V\,d\log\kappa.
\]

For any independent rational base field \(D\) satisfying

\[
\operatorname{div}D=0,\qquad
D(\log\kappa)=\frac L{2c_0K^2},
\]

the exact current \(J=VU+PD\) therefore satisfies
\(\operatorname{div}J=R\). No fixed \(H,B,C\) directions have been assumed:
all their derivatives enter the scalar \(D(\log\kappa)\).

In the complete canonical two-component notation the currents are

\[
A_{\rm cur}=U+fD,\qquad B_{\rm cur}=D.
\]

The first complete equation is
\(\operatorname{div}A_{\rm cur}+(3/t_0)D(\log\kappa)=0\), and the second
is exactly \(1/(HC)\). Although \(\operatorname{div}B_{\rm cur}=0\), this is
not the pure-W restriction: \(A_{\rm cur}\) remains present. In fact

\[
\operatorname{div}A_{\rm cur}
=-\frac3{t_0}D(\log\kappa)
\]

is generically nonzero. Also
\(A_{\rm cur}(\log\kappa)=-1/(2HC)+fL/(2c_0K^2)\) is not identically
zero, as an exact rational-point check confirms. Thus the earlier necessary
coupling conditions are respected. They do not rule out this conditional
construction.

The Hamiltonian option in the constructive note is sufficient and narrower
than the general divergence-free field: for the stated positive bracket,
\(D=(-S_h,S_Z,-S_v,S_u)\) has zero divergence and
\(D(G)=\{S,G\}\). A rational solution to its remaining Hamiltonian equation
has not been produced and is not implied by local analytic integration.

`verify_coupled_euler_fraction.py` independently passed twelve exact audit
groups using Fraction Laurent arithmetic, including all physical factors,
the operator split and both complete current coefficients. If \(D\) is
found, the result is already an actual finite-function-field current and can
use the verified source-to-witness transfer. Its exported exact polynomials,
denominator and Lean verification would still need to be completed. No
certificate has been found.
