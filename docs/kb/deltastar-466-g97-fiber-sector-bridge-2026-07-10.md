# Issue #466/#505 G97: the fiber–sector bridge and the shallow centered discharge

Date: 2026-07-10

Two towers stood without touching: the analytic tower (`depthFiber`, welded to `DCEnergyBound`
by G96) and the counting tower (the relativized G88 `MaxCancellationCollisionSector` over an
injective value map, post-`cdd69c676`). G97 is the bridge, plus the shallow discharge.

## Results (`Frontier/_G97RelativizedSectorBound.lean`, 8 declarations, axiom-clean, 0 sorryAx)

- `map_inter_of_injective`, `card_leftCore_map` (upstreamable multiset bricks): multiset
  intersection commutes with an injective map; hence G83M maximal-cancellation depth is
  invariant under injective value maps.
- `depthFiber_le_sectorCard` (**the bridge**): the depth-`s` slice of the `G`-supported
  equal-sum pair cube injects into `MaxCancellationCollisionSector {x // x ∈ G} F Subtype.val`.
  So the object G96 feeds to `DCEnergyBound` is bounded by the object the G86/G87/G88 decoder
  chain counts.
- `depthFiber_le_correctedPadEnvelope`: for `1 ≤ s ≤ r` the TRUE fibers satisfy the
  `#G^(2s-1)`-core corrected envelope — the G89/G96 interface hypothesis is now a theorem at
  every positive depth.
- `depthFiber_zero_eq` / `centered_bound_zero`: depth 0 is an identity (equal bags force equal
  sums): its centered bound is free with any cap.
- `depthFiber_zero_le_envelope`: the depth-0 fiber obeys the `s = 0` corrected envelope
  `r! · #G^r` (subsingleton core count).
- `production_shallow_caps_affordable` (kernel): at `(#G, r) = (2^30, 110)` the corrected
  envelope caps at depths 0–3 (core counts `1, n, n^3, n^5`) total under one Wick budget.

## Net effect (G96 + G97)

In `dcEnergyBound_of_centered_depth_bounds`, take `cap s` = the corrected envelope for
`s ≤ 3` and anything affordable for deeper `s`. The hypotheses at depths 0–3 are now theorems
(G97 envelope bounds imply the centered form since a cap bound is stronger than cap + allowance).
Production `DCEnergyBound` ⟸ centered per-depth bounds for `4 ≤ s ≤ 110` only, with an
explicitly computed residual Wick budget. The wall is now exactly depths ≥ 4 — matching, from
the analytic side, the depth-four cutoff the counting side found (G82/G89), and refining the
whole programme to one quantified family of centered inequalities.

## Honest scope

Deep centered bounds (`4 ≤ s ≤ 110`) remain the open analytic wall. CORE remains OPEN /
ON-BGK.
