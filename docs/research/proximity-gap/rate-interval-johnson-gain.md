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
