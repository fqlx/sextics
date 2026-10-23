# Physical-discriminant current operator audit

Inspected `endpoint/quotient/physical_discriminant_correction.py` against the
exact moving-pole and quotient connection conventions. No operator discrepancy
was found. This audit does not rerun or enlarge the restricted search.

For a finite endpoint pole \(s(q)\), put \(F_s=f(s)\). Its connection diagonal
is
\[
b_i=-\frac{\partial_iF_s}{2F_s}.
\]
This includes derivatives of the physical pole location. A compact current
\(P_i/F_s\), after multiplying its covariant divergence by \(F_s\), gives
\[
\partial_iP_i+B_iP_i-\frac{\partial_iF_s}{F_s}P_i
=\partial_iP_i+B_iP_i+2b_iP_i.
\]
Thus the factor two in the implemented compact block is required.

For a potential vector \(A\), define
\[
V=\operatorname{curl}A-\frac{\nabla F_s\times A}{2F_s}
  =\operatorname{curl}A+b\times A.
\]
Because \(b=-\tfrac12\nabla\log F_s\) is a closed rational one-form,
\[
\operatorname{div}V+b\cdot V=0.
\]
The finite-pole row therefore vanishes identically, while its compact output is
\(\sum_iV_iB_i e_\beta\). Multiplication by \(F_s\) gives exactly the
implemented potential block. The infinity-residue row is retained among the
five free compact rows. The right side is the actual source
\(-F_sM_He_0/18\) on \(X_0=1\).

With quotient coordinate weights \((2,3,1)\), compact basis index \(j\), and
extra \(X_0\)-denominator degree \(k\), the free numerator degree is
\(12+k+w_i-3-2j\). Potential component \(A_j\) has numerator degree
\(k+5-w_j\). These give the required total current degree. The displayed
parities are correct: compact numerator parity \(j+1\), and potential
numerators odd under \((u,v,z)\mapsto(-u,-v,-z)\). The homogeneous source has
the additional \(X_0^3\) factor described in the endpoint interface audit.

Any consistent evaluation matrix still needs exact coefficient reconstruction
and literal candidate verification. No current or certificate follows from
these operator checks alone.
