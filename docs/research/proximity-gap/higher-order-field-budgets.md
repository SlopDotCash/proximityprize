# General-order hidden-derivative estimates at production length

For capacity slack `g`, derivative order `d`, total jet degree `v` and
challenge height `h`, the canonical symbolic-curve theorem bounds the number
of bad line challenges by `C(g,v,h,d) n^(d+1)`. If `0<g≤1/s`, the smallest
possible coefficient in this range equals

$$
h+(2s)^d v^{d+2}\big(sh(d+1)(3d+5)+3\big).
$$

The bound follows by monotonicity in `1/g` and is attained at `g=1/s`.
Multiplying this integer by `Q n^(d+1)` and comparing it to `p` decides
whether the envelope can meet tolerance `1/Q` for some such slack. A
symbolic equation of the required degrees is an additional interpolation
requirement.
[Lean integer equivalence and named budgets](../../../ArkLib/Research/ProximityGap/Frontier/HigherOrderFieldBudget.lean) · [Canonical product coefficient](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/ProductCounting.lean)

Take `n=2^30`, `Q=2^128` and `p<2^256`. With `v,h≥1` every feasible order
is at most two. Already at `d=3` and the most favorable admissible slack
`g=1` the least coefficient is 473, whereas the field budget allows fewer
than 256 units of `n^4`. At `d=2` and `g≤1/4` the complete necessary
inequality becomes

$$
2^{218}\big(h+(8448h+192)v^4\big)\le p.
$$

The implied ceilings on `h v^4` are 35 in the 237-bit witness field, 16,135
in the field of order `65·2^239+1`, and 14,734,505 in the BLS12-381 scalar
field. For positive height these give `v≤2,11,61`, respectively. Sharper
geometric or order-specific stage counts can change the envelope.

## Fixed capacity slack and the prize budgets

Jeronimo's Theorem 1.2 treats ordinary, unfolded Reed–Solomon codes on every
prescribed prime-field domain. It fixes a positive capacity slack and curve
degree before choosing the minimum length and polynomial exponent. Theorem
1.1 gives field-independent polynomial list size for sufficiently large
length. Corollary 8.3 obtains both grand-challenge inequalities for fixed
width and security parameter when the field exceeds the stated polynomial
budget. The paper explicitly leaves the largest safe radius and shrinking
slack open. The hypothesis allowing linear-size fields for the list decoder
does not bound the fraction of bad affine-line challenges by `2^-128` there.
ArkLib's capacity theorem provides the same fixed-slack qualitative route,
with a concrete polynomial exception estimate whose finite-budget
restrictions are quantified above.
[Jeronimo, Theorems 1.1–1.2 and Corollary 8.3](https://arxiv.org/html/2609.05870v1) · [Local copy](../../../research/jeronimo-2609.05870.pdf) · [Prime-field specialization of the canonical capacity theorem](../../../ArkLib/Research/ProximityGap/Frontier/PrimeFieldCapacityGap.lean)

## Full jet simplices at half rate

For derivative order `d≥2`, consider all monomials of a given total degree
`t` in the `d+1` jet variables. In the local Taylor model over `F[T]/T^m`,
replace the value variable by its difference from the backward Taylor sum.
This triangular change of variables is invertible on complete homogeneous
layers. The new value variable maps to `T^(d+1) E`. When the coordinate
powers from `0` to `m−1` are present in all monomials, the monomial of
residual exponent `j` has rank `(m−(d+1)j)₊`. The surviving powers of `T`
and distinct monomials in `E` and the derivative variables are independent,
in every characteristic.

At order two, the local rank at degree `t` is
`Σ_{j=0}^t (t−j+1)(m−3j)₊`. It is at least
`choose(t+2,2)(3m/4−t/2)`. For `t=2l`, retain the terms through `j=l−1`
and three quarters of the term `j=l`. For `t=2l+1`, retain the terms
through `j=l` and one quarter of the term `j=l+1`. The retained mass is
three quarters of the complete layer in either parity. Its first moment
is at most `t choose(t+2,2)/6`. Dropping the positive-part restriction
on just these retained terms proves the inequality.

At higher order, condition on the total degree of the first three
coordinates. In an unrestricted homogeneous layer its mean is `3t/(d+1)`
by stars and bars. The order-two calculation with contact `d+1` gives the
same lower bound per monomial, `3m/4−t/2`. At half rate, when `n≥4(d+1)`
and `A≤3n/4−2(d+1)`, granting all monomials the most favorable coordinate
weight `k−(d+1)` still leaves their column count at most `n` times this local
rank. The inequality remains true under every nonnegative choice of weights
on entire layers, including challenge-degree weights.

For a layer truncated in coordinate degree before `m`, the widths in one
homogeneous layer vary by at most `dt`. The pure highest derivative at
maximal width `L` supplies at least `min(m,L)` independent coordinate
powers. If `t≤2m` and `choose(t+d,d)(1+2d)≤n`, these alone cover the
partial layer's columns. Under the same agreement bound, `t>2m` gives no
columns. Lean proves the rank-profile inequalities, their binomial moments,
the weighted sum and the clipped-layer arithmetic. The Taylor coordinate
change identifying the fully occupied profile with the actual local rank is
the algebraic argument above. Proper subsets of the derivative monomials
can have smaller rank; Jeronimo and BCPZZ explicitly use restricted supports.
[Lean simplex calculation](../../../ArkLib/Research/ProximityGap/Frontier/SecondOrderSimplexFloor.lean) · [Brakensiek, Chen, Putterman, Zhang and Zheng](https://arxiv.org/abs/2609.08005)
