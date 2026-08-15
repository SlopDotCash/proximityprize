# Issue #466/#507 G135: census family ⟹ per-frequency sup bound — end-to-end

Date: 2026-07-11 (UTC). `Frontier/_G135CensusToSupBound.lean`, axiom-clean, 0 sorryAx,
first-pass compile.

## Result

`eta_pow_le_of_census_family`: for the production subgroup (#G = 2^30, q ≤ 2^160) with a
primitive additive character, under
- the disjoint-census family (`2·q·depthFiber G t t ≤ 2·q·Wick_t + n^{2t}`, 11 ≤ t ≤ 110), and
- the low-rung anchors (DCShape at t ≤ 10),

every nontrivial Gauss-period frequency satisfies `‖η_b‖^220 ≤ q·(219!!·n^110)` — i.e.
`M ≤ (q·219!!·n^110)^{1/220} ≈ 2^19.7` (vs trivial 2^30; prize target ≈ 2^18.4 after
moment-order optimization, which the in-tree machinery can tune).

## Significance (#507 shape)

This is the end-to-end conditional statement on the census face: wall-hypothesis family
(finite, per-prime, counting-flavored) → analytic sup-norm control consumed by the prize
threshold chain, all intermediate steps axiom-clean (G89→G135). Together with G134's audit,
the full conditional structure of this face is: census family (no evidence against) +
anchors t = 2..10 (open, bump at 5–6, prime-individual) ⟹ per-frequency moment bounds.

CORE remains OPEN.
