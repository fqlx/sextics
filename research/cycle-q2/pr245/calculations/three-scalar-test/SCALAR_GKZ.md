# Holomorphic scalar representative in the plane-sextic fibration

Take the normalized curve
F=A Y^6+B X^6+XY+X+Y+C=0, and ωᵢⱼ=[XⁱYʲ dX/F_Y], including ω₀=ω₀₀.
Write θ_A=A∂_A, θ_B=B∂_B and
Lx=5θ_A−θ_B−C∂_C, Ly=−θ_A+5θ_B−C∂_C,
Lxy=−5θ_A−5θ_B+C∂_C.

The polynomial identity X−Lx(F)=F−YF_Y gives
∇_C ωᵢ₊₁,ⱼ=(∇_Lx+j)ωᵢⱼ.
Indeed multiplying the right-hand polynomial identity by XⁱYʲ/F²
gives the derivative ∂_Y(XⁱYʲ⁺¹/F) plus the indicated residual numerator.
Equivalently use the implicit lift at fixed X, ∂_C Y=−1/F_Y. For j=0
the fixed-X densities themselves agree: X−Lx(F)=−YF_Y on the curve,
and Lx acting on the coefficient polynomial F_Y gives Y F_YY.

By interchanging X,Y one obtains ∇_C ωᵢ,ⱼ₊₁=(∇_Ly+i)ωᵢⱼ in cohomology.
The relation XY−Lxy(F)=XF_X+YF_Y−F yields ∇_Cω₁₁=(∇_Lxy−1)ω₀.
Since [∂_C,Lx]=[∂_C,Ly]=−∂_C and [∂_C,Lxy]=∂_C, these equations imply

    ∇_C²ω₂₀=(∇_Lx−1)∇_Lxω₀,
    ∇_C²ω₁₀=(∇_Lx−1)∇_Cω₀,
    (∇_Lx∇_Ly−∇_Lxy∇_C)ω₀=0.

Two sixth-order box operators follow from ∂Bω₀=∂Cω₆₀
and ∂Aω₀=∂Cω₀₆:
∇_C⁵∇_Bω₀=∏_{j=0}⁵(∇_Lx−j)ω₀ and
∇_C⁵∇_Aω₀=∏_{j=0}⁵(∇_Ly−j)ω₀.

Now set t=τ, A=2t⁴/b⁵, B=2T³/(t⁵b⁸), and
l=2b/t², m=2tbT, n=2tb/T, z=2tb⁴/T, C=l+m+n+z.
Define V=5t∂t+4b∂b+19T∂T, U=−b∂b−3T∂T, E=V(C),
r=3(m−n)/E. Then ∂_C=V/E, Lx=U+rV. For the measure
dlog t∧dlog b∧dlog T both U and V have divergence zero. With
g=4T/(3tb²), g₁=16b²=6zg and U(g)=−g, U(g₁)=−2g₁,
integrating by parts the explicit two source terms

    g∇_C²ω₂₀+g₁∇_C²ω₁₀

gives the single holomorphic term hω₀, with

    h = V( U(rg) + r V(rg) − (g₁−V(rg₁))/E ).

In this equality the omitted three-form currents are explicit applications
of the covariant product rule and the two indicated vector fields.
At t=b=T=1 one has E=28 and h=−3336/7. The rational identities can be
checked with one_scalar.py. A primitive for h·ω₀ on the total fourfold
has yet to be determined.

The first-order geometric variation on this holomorphic vector has
full rank three: the degree-nine Jacobian ideal of the projective sextic
has at most 45 independent degree-four multiples of its partials.
At (A,B,C)=(2,3,5) modulo 101 these 45 rows have rank 45, and appending
X⁶Z³,Y⁶Z³,Z⁹ makes rank 48. Thus the three parameter derivatives of ω₀
are independent in the generic lower Hodge quotient. See rank_higgs.py.

There is also a local restriction on using the quadratic box alone.
For the logarithmic measure its fourth pole along simple ramification E=0
for a regular multiplier a has coefficient
3a(VE)²·K with K=Nx Ny−Nxy, Nx=3(m−n), Ny=3(n−3m), Nxy=−m+n−2z.
These are the coefficients in Lx=U+Nx V/E, Ly=U'+Ny V/E and
Lxy=U''+Nxy V/E, using U'=t∂t+b∂b+6T∂T, U''=b∂b+T∂T.
The source has leading coefficient 3g(VE)²·Nx(Nx+6z).
At n=2m, l=8m/(6−m³), z=4m⁴/(6−m³), take a real root of
3m⁴−3m³−18m+2=0 in (0,1/8). These values satisfy z=lmn²/8
and define a genuine torus point after extracting the monomial roots.
There E=K=0 with VE>0; Nx=−3m and Nx+6z=−27m².
Therefore no multiplier regular at this point can give the source as
the formal adjoint of this single quadratic relation. This does not
exclude multipliers with new poles, high-order boxes, or general currents.
