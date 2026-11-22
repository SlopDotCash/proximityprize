# One percentage point beyond finite Johnson throughout a rate interval

Let `n≥4096` and `n/16≤k≤n/2`, with integer block length and dimension. For
every injective prime-field evaluation domain, set

$$
\delta=1-\sqrt{(k-1)/n}+1/100.
$$

The affine-line MCA error at this closed radius is at most `2^31 n²/p`.
Thus `p≥2^159 n²` suffices for 128-bit security. At `n=2^30` this asks for
`p≥2^219`. At the same radius the complete list at every center and every
finite interleaving width contains at most `174000 n` words over every prime
field admitting the domain. The numerical field-size condition applies to
the probability target. The scalar list also holds in characteristic zero
and in any field of characteristic at least `n`.
[Lean theorems](../../../ArkLib/Research/ProximityGap/Frontier/RateIntervalJohnsonGain.lean)

## Four affine inequalities

For a first-order profile of multiplicity `m`, derivative cap `M`, total jet
degree `v` and challenge height `h`, put `w(t)=(min(t,M)+1)(h+1−t)` for
`0≤t≤v`. Let `R` be the number of constraint slots at a single received
site, `B=Σ t w(t)` and `C=m Σ w(t)`. The positive parts in the column count
give at least `C A−B k` available interpolation slots. Consequently
`Rn+Bk<CA` suffices at any length `n`, dimension `k` and agreement count `A`.

| Range of `3000 sqrt((k−1)/n)` | m | M | v | h | R | B | C |
|---|---:|---:|---:|---:|---:|---:|---:|
| 747–1125 | 12 | 6 | 36 | 672 | 256746 | 3000634 | 1866564 |
| 1125–1500 | 16 | 7 | 33 | 320 | 244296 | 1322636 | 1182272 |
| 1500–1875 | 24 | 9 | 39 | 368 | 789025 | 2629060 | 2959560 |
| 1875–2125 | 40 | 12 | 55 | 1024 | 8251334 | 19488326 | 25860640 |

Write `x=sqrt((k−1)/n)` and choose `A=floor((x−1/100)n)`. On each listed
interval, comparing `x²` with its secant line gives
`R+Bx²<C(x−11/1000)`. The extra `1/1000` absorbs rounding in `A` and the
single degree of difference between `k` and `k−1`, since `n≥4096` and
`B≤2C`. The same comparison yields `(n−k)≤6(A−k)` and `k+1≤3(A−k)`.
The first inequality bounds the incidence ratio in the MCA charge. The
second bounds the list weight. A rational-function extension transfers the
scalar list bound to every interleaving width.
[Closed slot counts](../../../ArkLib/Research/ProximityGap/Frontier/FineGridFirstOrderSecurity.lean) · [Canonical first-order field recovery](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/AutomaticHybrid.lean)

## Every fixed physical rate

Let `0<R<1` and `g(R)=3 sqrt(R)(1−sqrt(R))²/32`. The canonical
first-order agreement threshold `a₁(R)` satisfies `a₁(R)+2g(R)≤sqrt(R)`.
Indeed, put `x=sqrt(R)` and `s=sqrt(R(5−R)(2−R))`. Rationalizing the
threshold gives

$$
(x-a_1(R))(x(8-R)-3R+2s)=3R(1-x)^2.
$$

The second factor is positive and at most `16x`. Taking agreement
`sqrt(R)−g(R)` therefore leaves at least `g(R)` of interpolation slack.
For the explicit rate-only coefficients `E(R)` and `M(R)` in ArkLib's
exception and multiplicity estimates, put
`C(R)=max(E(R)/g(R)^5, 1+M(R)/g(R))`. For every integer `Q≥1`, prime
`p≥Q C(R)n²`, prescribed domain and `2≤k≤Rn`, the line-MCA error at
`1−sqrt(R)+g(R)` is at most `1/Q`. At the actual rate `R=k/n`, the length
condition `n sqrt(R) g(R)≥2` gives the same bound at the finite-length
Johnson radius plus `g(R)/2`. No rate restriction beyond `0<R<1` enters
this statement. The four-profile bound above gives a smaller explicit field
requirement throughout its specified interval.
[Every-rate Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/EveryRateJohnsonGain.lean) · [Canonical coefficients](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/AutomaticBounds.lean)
