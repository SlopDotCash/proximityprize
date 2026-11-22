# Scaled squarefree MCA bounds on prescribed prime-field domains

Let `n=4096b` with `b≥1`, and let the Reed–Solomon dimension be exactly
`n/2`, `n/4`, `n/8` or `n/16`. Each row below applies to every
injective evaluation domain in the indicated prime field and every received
pair. The first numeric column gives the error radius in units of `1/4096`.
For its exponent `s` the bad-scalar probability is at most `2^s n²/p`
under the characteristic condition for first-order recovery. In particular,
the 128-bit target holds when `p≥2^(128+s)n²`.

| Rate | Error numerator | s | Multiplicity | Derivative cap | Total jet degree | Challenge height |
|---:|---:|---:|---:|---:|---:|---:|
| 1/2 | 1266 | 36 | 251 | 77 | 346 | 31113 |
| 1/4 | 2171 | 37 | 251 | 113 | 471 | 43219 |
| 1/8 | 2785 | 37 | 251 | 138 | 642 | 71065 |
| 1/16 | 3199 | 37 | 235 | 154 | 822 | 80393 |
| 1/2 | 1269 | 44 | 888 | 275 | 1225 | 392510 |
| 1/4 | 2174 | 42 | 635 | 288 | 1191 | 327767 |
| 1/8 | 2788 | 45 | 950 | 523 | 2426 | 877596 |
| 1/16 | 3201 | 41 | 520 | 343 | 1817 | 400286 |
| 1/2 | 1270 | 55 | 5874 | 1825 | 8105 | 17350380 |
| 1/4 | 2175 | 47 | 1424 | 647 | 2671 | 1546424 |
| 1/8 | 2789 | 58 | 7697 | 4236 | 19648 | 75007065 |
| 1/16 | 3202 | 47 | 1331 | 878 | 4647 | 2753034 |

## Normalizing the canonical exception bound

Use a reference length `N`, dimension `k`, and agreement count `A`.
A strict surplus in the received-line interpolation slots persists when all
three block parameters are multiplied by any positive integer `b`.
Put `θ=(N−k)/(A−k)`. At the scaled message degree `D=bk−1` the
canonical ratio is `(b(N−k)+1)/(b(A−k)+1)≤θ`. Let `v,M,h` denote total
jet degree, derivative cap and challenge height, and set `f=v(2M+1)`,
`g=h(2M+1)`. Canonical squarefree recovery bounds a single exceptional
set for all candidate polynomials of each received pair. Substitute
`D≤bk` and `bN−D−1≤bN` in its finite-length envelope, where the block
length in that envelope is `bN`. The resulting constant, linear and
quadratic terms in the scale are each bounded by `b²` times their value
at scale one. Thus the bad-scalar count is at most `b²` times

$$
(2f-1)g+\theta(g+f+4kfg)+Nf+
 (48k^2h+16k)\theta^2 vM+8kN\theta vM.
$$

Every table row checks that this expression is at most `2^s N²`. The
result also applies at any other rate and reference length when the
same explicit slot and charge inequalities hold. The first-order
certificate and the geometric recovery are the canonical ArkLib results.
[Scaled Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/ScaledSquarefreeSafety.lean) ·
[Canonical finite-length envelope](../../../ArkLib/Data/CodingTheory/ReedSolomon/ListDecodability/FirstOrder/FiniteLengthParameters.lean) ·
[Reference-length scaling](../../../ArkLib/Research/ProximityGap/Frontier/FineGridFirstOrderSecurity.lean)

## Comparison at production length

The previous arbitrary-domain estimates at `p≥2^165 n²` had numerators
1262, 2166, 2780 and 3195. At precisely that requirement the first four
rows increase them by 4, 5, 5 and 4 grid units, respectively. The middle
four rows recover all the previous wide radii with the common requirement
`p≥2^173 n²`, lowering its exponent from 180 by seven.

At `n=2^30` the last four rows fit the BLS12-381 scalar modulus and raise
all four old wide numerators by one grid unit, or 262144 errors at each
rate. The same conclusion holds in the 246-bit prime field of order
`65·2^239+1`. At eighth rate in that field the scale-one terms are bounded
at reference length 8192 with doubled agreement and dimension. This lowers
its required exponent from 186 to 185. The older small-length exact BLS
list and MCA results concern different domains and radii.
[Previously verified production intervals](../../../ArkLib/Research/ProximityGap/Frontier/FineGridProductionMcaIntervals.lean) ·
[New field-specific endpoints](../../../ArkLib/Research/ProximityGap/Frontier/ScaledSquarefreeSafety.lean)
