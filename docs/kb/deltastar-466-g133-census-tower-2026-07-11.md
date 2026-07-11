# Issue #466 G133: THE CENSUS TOWER — the whole DC hierarchy from the disjoint-census family

Date: 2026-07-11 (UTC)

Capstone of the descent programme (G121→G132). `Frontier/_G133CensusTower.lean`,
4 declarations, axiom-clean, 0 sorryAx, compiled clean on first pass.

## Results

- `DCShape F G s`: the ℕ-clean DC form `q·E_s(G) ≤ q·(2s−1)!!·n^s + n^{2s}` at #G = 2^30.
- `perRung_census_gate`: at every rung 11 ≤ t ≤ 110, `DCEnergyBound G t` ⟸ DCShape at the
  eight predecessor rungs + the rung-t disjoint census fitting Wick + half the DC mass
  (`2·q·depthFiber G t t ≤ 2·q·Wick_t + n^{2t}`).
- `dc_tower` (strong induction, descending 8 rungs per step): DCShape holds at ALL rungs
  t ≤ 110 from the census family (rungs 11..110) + low-rung anchors (t ≤ 10) alone.
- `dcEnergyBound_of_census_family`: `DCEnergyBound G t` for every 11 ≤ t ≤ 110 from the
  same data.

## What this means

**The entire production DC hierarchy at a certified prime (q ≤ 2^160, #G = 2^30) is now
formally equivalent-in-consumption to one family of disjoint-support census statements plus
ten low-rung anchors.** Every intermediate object — corrected decoders (G86–G88), weighting
semantics (G95), moment welds (G96), fiber–sector bridges (G97), descent identities and
ladders (G121/G123), the moment LP and its dual (G124/G127), isolation (G125), the census
gate (G126), and all budgets (G128–G132) — is unconditional, axiom-clean, with kernel
constants. The prize chain (M ≤ √(2n·ln q) via eta_pow_le_of_dcEnergyBound at the optimized
rung) consumes DCEnergyBound directly.

## The wall, in final coordinates

1. The disjoint-census family: for each rung 11 ≤ t ≤ 110, the fully-disjoint equal-sum
   census `depthFiber G t t` exceeds `Wick_t + n^{2t}/(2q)` by nothing — the exact
   square-root-cancellation content, now per-rung, per-prime, with all plumbing done.
2. Low-rung anchors t ≤ 10 (the rung-2 anchor exists in-tree; 3..10 open).

No claim any of these hold. CORE remains OPEN — but its statement has never been this
localized.
