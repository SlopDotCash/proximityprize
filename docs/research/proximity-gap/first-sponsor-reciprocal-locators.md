# A one-step first-sponsor incidence improvement via reciprocal locators

Author: Mikhail Izhutkin (mashingaan). AI assistance via OpenAI Codex.

This is a mathematical proof draft. The end-to-end Lean theorem remains open.

## Statement and witness reduction

For the exact first-sponsor evaluation code of length `n = 1073741824` and degree bound `n - D = 536870911`, take `D = 536870913` and `t = 221512374`. No family of `b = n+1` canonical bad heads can have error weight at most `t` per head. This is the incidence assertion at radius `t/n`. The same conversion used by `firstPrime_constant_floor` would give the floor `(t+1)/n` for the canonical `mcaDeltaStar`.

Use the exact error sets `E_i` against the received affine pencil. If a canonical witness initially gives only a subset of the agreement coordinates, enlarge it to the exact agreement set. The no-joint-explanation condition persists under enlargement. Take distinct scalar parameters and `b` heads. The existing `bad_witness_line_cap_three` applies since `7t < 3D` and `t+1 < b`. The rich-line disjointness theorem in #840 then gives at most `floor(b/3)` unordered collinear triples, since `2t < D`. All other triples have error union of size at least `D` by the code distance. Call a noncollinear triple tight if its error union has size exactly `D`, and call a triple long if its error union has size at least `D+1`.

## Restricting tight completions of a pair

Fix two heads `a,b` with distinct parameters `alpha,beta`, and put `E = E_a union E_b`, `e = |E|`, `k = D-e`, and `l = D-2t`. For each tight completion `c`, with parameter `gamma`, the error union is `S_c = E union E_c`. Remove at most two completions so that neither cross triple on `a,c,d` or `b,c,d` is collinear for any surviving pair `c,d`. Each of `a,b` belongs to at most one collinear triple, so there are at most two forbidden pairs of completions and deleting one endpoint per pair suffices. The four-set separation bound in #842 gives `|S_c minus S_d| >= l` for surviving pairs. In particular, all surviving supports differ.

Interpolate the code pencil `p(z) + gamma*r(z)` through `a,b`. Off `E` it matches the received pencil, as two affine functions in the scalar parameter agree at two distinct values. For a surviving `c`, its residual polynomial `v_c` from that code pencil is nonzero by noncollinearity. It vanishes off `S_c` and has degree at most `n-D`. Thus it has degree exactly `n-D`, has precisely those `n-D` evaluation roots, and is nonzero throughout `S_c`. Write `P(z)` for the product of `z-x` over evaluation points outside `E`, and `L_c(z)` for the monic product over the `k` points in `S_c minus E`. There is a nonzero scalar `lambda_c` with `v_c L_c = lambda_c P`.

On `E_a minus E_b` the received pencil minus the interpolated code pencil is `(gamma-beta) d_b(x)` for a nonzero slope `d_b(x)`. On `E_b minus E_a` it is `(gamma-alpha) d_a(x)`, again with nonzero slope. These facts follow from agreement at the correct head and disagreement at the other. Define

```
q_c = (gamma-beta) L_c / lambda_c
eta_c = (gamma-beta)/(gamma-alpha)
```

Both denominators are nonzero. The map from `gamma` to `eta_c` is injective because `alpha != beta`. When `c` agrees with the received pencil at a point in the symmetric difference of the two error sets, the equation for `v_c L_c` gives `q_c(x) = P(x)/d_b(x)` on the first part and `q_c(x) = eta_c P(x)/d_a(x)` on the second. Thus the degree-at-most-`k` locator heads agree with a new affine received pencil there. Each has at most `u = t-k` errors on this symmetric difference, since exactly `k` of its original errors are already spent outside `E`. The symmetric difference has at least `L = 2(e-t)` points. Restrict to any `L` of them.

A noncollinear triple of locator heads has at most `k` common agreements in this restriction. Indeed the residual from the interpolant through two of them is a nonzero polynomial of degree at most `k` and vanishes at every common agreement. Any locator line through two or more surviving heads contains at most 11. Its polynomials are distinct since their monic locators have distinct root sets. The roots common to two of the polynomials are roots of every polynomial on that line, and all remaining root sets are disjoint across heads. If the common root count is `r`, separation gives `k-r >= l`, so the number of heads on the line is at most `n/l < 12`.

Let `m` be the surviving completion count and let `f_x` count locator agreement at a restricted coordinate. Repeated-index ordered triples number at most `3m^2`. Ordered collinear distinct triples number at most `9m(m-1)`, because each ordered pair has at most nine additional heads on its line. Therefore

```
L (m(1-u/L))^3 <= sum_x f_x^3 <= k m^3 + 12 L m^2.
```

Take `e0 = 377420252`. For `e >= e0`, put `s=e-t`, so that `s >= l`. The margin `L(1-u/L)^3-k` is `(s+l)^3/(4s^2) - (D-t-s)`. Its derivative is `(5-3(l/s)^2-2(l/s)^3)/4 >= 0`. At `e0` the margin exceeds `778467`, and `L <= 2t` for any pair. Hence `m < 6830` and every pair with `e >= e0` has fewer than `7000` tight completions including the deleted ones.

## Global supply of pairs and contradiction

Let `M_x` count agreement heads at original coordinate `x`, and `B = b(b-1)(b-2)`. The sum of ordered distinct triple common agreements is at most `(n-D)B + 2Db`, because the at most `floor(b/3)` unordered collinear triples add at most `D` each. Therefore `sum_x M_x^3 <= U`, where `U = (n-D)B + 2Db + 3nb^2`, by allowing at most `3b^2` repeats. Furthermore `sum_x M_x >= b(n-t)`. For `q = 852229450`, the pointwise square bound `3q M_x^2 <= 2M_x^3 + q^3` follows from `(M_x-q)^2(2M_x+q) >= 0`. So the mean pair error-union size is at least

```
mu = n - ((2U+nq^3)/(3q) - b(n-t))/(b(b-1)).
```

Since all pair unions have size at most `2t`, a fraction at least `(mu-e0)/(2t-e0)` of unordered pairs have union size at least `e0`. Here `mu > 397326860`, and that fraction exceeds `0.30343`. Each high-union pair belongs to `b-2` triples, of which fewer than `7000` are tight and at most one is collinear. Count the remaining long triples through these pairs. Each is counted at most three times, so at least a fraction

```
((mu-e0)/(2t-e0)) * (b-2-7001)/(b-2) > 0.30
```

of all unordered triples are long. The distinct-triple excess inequality in #841 then contradicts the falling-cubic lower bound at `t`. This proves the stated mathematical incidence bound under the witness, line-cap and rich-disjointness lemmas above.

## Band of near-minimal supports and a 250,000-step improvement

The same reduction works for noncollinear completions whose error union has size in `[D,D+J]`. Take `J = 3100000`, `t = 221762374` and raise the high-pair cutoff to `e0 = 388694542`. For a completion with support size `D+j`, its outer support has size `k+j`, and factoring the evaluation roots outside that support gives

```
v_c L_c = h_c P,  deg L_c = k+j,  deg h_c <= j.
q_c = (gamma-beta) L_c / h_c.
```

Here `h_c` is a nonzero polynomial and `q_c` is a rational function. Every root of `L_c` is an actual outer error, where both `v_c` and its prescribed root factor are nonzero, hence `h_c` is nonzero at every root of `L_c`. In particular the zero set of `q_c` in the evaluation domain is exactly the outer support. At the agreement coordinates in `E_a` symmetric difference `E_b`, the same substitution for `v_c` is nonzero, so `h_c` is nonzero there and the transformed relation holds. Each completion still uses at most `t-k` errors on the restriction. For a noncollinear triple of rational locator heads, interpolate through two using the transformed scalar parameters and clear the three denominators. The resulting nonzero polynomial is of degree at most `k+3J`, so common agreements are at most `k+3J`.

After deleting at most two heads to exclude cross-collinear triples, the pointwise four-set inequality bounds the size of the symmetric difference of any two outer supports below by `2l`. Their sizes differ by at most `J`, so each one-sided difference has size at least `l-J/2`. For a rational locator line through two heads, any shared root of their numerators is a zero of all the other locator heads on the line. To see this at a potentially problematic coordinate, clear the three denominators in the affine combination and use that the first two denominators are nonzero there. This forces the third numerator to vanish there, and its denominator is then also nonzero. Thus the private roots remain disjoint. Each head on that line has at least `l-J/2` private roots by pairing with any other head. The line cap remains 11 since `12(l-J/2) > n`.

The local margin is the same function of `e` minus `3J` and is still increasing above the cutoff. At `e0` it exceeds `711794`. There are fewer than `7500` surviving near-minimal completions per high-union pair, since `24t / margin < 7500`. Allowing for the two deletions and at most one collinear triple costs at most `7503` completions per such pair.

The global estimate with `q = 851979450` gives a fraction greater than `0.1574` of triples with error union at least `D+J+1`, after the pair-to-triple count and all exceptional completions. Using only a fraction of `0.157` in the upper ledger subtracts `floor(0.157 * choose(b,3)) * (J+1)` common agreements. The falling-cubic lower bound still exceeds this upper ledger at `t = 221762374`. Consequently the mathematical incidence argument gives the lattice floor `221762375 / 2^30` on the same code. The rational-function transfer, aggregate counts, and their sponsor-facing integration still require end-to-end formalization.

## Weighting the excess by the common pair

The same rational locator argument gives a larger increase if the allowed width depends on the union size of the fixed pair. Take `t = 223512374`, `a = 397000000`, `q = 850229450`, `l = D-2t`, and `B = b(b-1)(b-2)`. For `e > t` put

```
F(e) = (e-t+l)^3/(4(e-t)^2) - (D-e).
W(e) = F(a) + F'(a)(e-a).
```

The function `F` is convex for `e > t`: writing `s=e-t`, its second derivative is `3l^2/(2s^3) + 3l^3/(2s^4)`. Thus `F(e) >= W(e)`. The slope `F'(a)` is positive and `W(t) < 100000`. For any pair with `W(e) >= 100000`, take `J(e) = floor((W(e)-100000)/3)`. This ensures `e > t`, `F(e)-3J(e) >= 100000` and `J(e) <= 20233794` since `e <= 2t`. The case in which no near-minimal completion exists requires no local construction. Otherwise `k=D-e` is nonnegative and the local construction above applies.

The rational locator line cap is now 15 because `16(l-J(e)/2) > n`. Even allowing `17m^2` repeated or collinear ordered triples, the surviving count is below `17 * 2t / 100000 < 80000`. Count the nonnegative surplus `max(0, errorUnionSize-D)` of each triple. For a pair as above, at least `b-2-80003` completions have surplus at least `J(e)+1`, after the two deletions and at most one collinear completion. For a pair with `W(e) < 100000`, the total surplus is nonnegative. Thus in both cases the total surplus over completions of the pair is at least

```
(b-2-80003) * ((W(e)-100000)/3 - 1).
```

Summing over all pairs counts each unordered triple three times. Since `W` is affine and increasing, the earlier bound `mu` on the mean pair union gives the following lower bound on the mean surplus:

```
(b-2-80003)/(b-2) * ((W(mu)-100000)/3 - 1) > 4000000.
```

Here the same formula for `mu` gives `mu > 397323129`. On the other hand the gap between the no-surplus common-agreement upper bound and the falling-cubic lower bound at this radius is less than `3800000` coordinates per triple. This last comparison uses the upper bound `2Db` on the ordered collinear contribution even if `b/3` is not integral. Subtracting the mean surplus gives a contradiction. Hence this weighted version gives a candidate lattice floor of `223512375 / 2^30`, which is 2,000,001 steps above the existing formal floor. The same end-to-end formalization obligations apply.
## The mean pair-union ledger is machine-checked

The weighted section above divides a sum over pairs by `b(b-1)` and calls the
result the mean pair-union size. Both halves of that step are now Lean theorems
in [`_PairUnionMomentMean.lean`](../../../ArkLib/Research/ProximityGap/Frontier/_PairUnionMomentMean.lean):

- `sum_card_inter_eq_sum_degree_sq` identifies the ordered pair-intersection
  mass with the sum of squared agreement degrees,
  `sum_card_inter_erase_eq_sum_degree_mul_pred` removes the diagonal and leaves
  the falling square `M (M - 1)`, and `ordered_pair_union_deficit` turns that
  into the ordered pair-union total `b (b-1) n - sum_{i != j} |E_i union E_j|`;
- `three_mul_sq_le` proves `3 q M^2 <= 2 M^3 + q^3` from
  `(M - q)^2 (2 M + q) >= 0`, and `sum_three_mul_sq_le` sums it against the
  cube budget;
- `mean_pair_union_moment` combines the two: an upper third moment `U` and a
  lower agreement mass `g` give
  `3 q (b (b-1) n - pairUnionTotal + g) <= 2 U + n q^3`.

That last inequality is exactly the `meanNum`/`denom` comparison the weighted
certificate consumes, so the mean bound `mu` is no longer an assumed step. The
local completion count, the sum of the local counts over pairs, and the
transfer to a sponsor-facing floor are still written arguments.

## Successor radius at the exact ledger gap

The published certificate compares a round mean surplus `4,000,000` against a
round ledger gap `3,800,000`. The gap grows with the radius, so the successor
certificate carries the exact gap. At `t = 223580000`, `a = 397300000` and
`q = 852000000` every condition still holds with a single round bound
`3,900,000`:

| Quantity | Value |
|---|---|
| Mean pair-union bound `mu` | `397326811.596` |
| Mean surplus per unordered triple | `3931501.0` |
| Ledger gap per ordered triple | `3898095.9` |
| Band cap `W(2t) - 100000` | inside `3 * 20233795` |
| Locator line cap | `16 (l - 20233794/2) > n` |

`first_sponsor_weighted_locator_margins_successor` checks all eight conditions
in exact integer arithmetic. Reproduce with

```
python3 scripts/probes/probe_weighted_locator_certificate.py --frontier
```

which also reports the ceiling of this argument: with the tangent point placed
at the largest admissible value the exact-gap comparison closes up to
`t = 223591047` and fails at the next integer. The ceiling is set by the ledger
gap, not by the band cap. The candidate floor therefore rises from
`223512375 / 2^30` to `223580001 / 2^30` with the arithmetic checked, and to
`223591048 / 2^30` as the exact-arithmetic limit of the same written argument.
Both numbers inherit the local-counting obligations stated above; neither is a
sponsor-facing result.
