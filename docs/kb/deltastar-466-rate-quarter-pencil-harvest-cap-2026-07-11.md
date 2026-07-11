# δ* #466 — Pencil harvest cap: the ratio-collision mechanism is a dimension count; three- and four-pencil `StallResidual` budgets are theorems under margin hypotheses (2026-07-11)

**Lane:** P1 rate-quarter predecessor pin — direct follow-up to
`deltastar-466-rate-quarter-stall-band-census-2026-07-11.md` (extremal stall families
= two-pencil covers at capacity `2(N−T+1)`; open corridor = families needing ≥ 3
pencils inside the slack `2T−N−2 = 111848106 ≈ 0.104·N`).
**Probe:** `scripts/probes/probe_rate_quarter_p1_pencil_harvest_cap.py` (exact
integer linear algebra mod `q`, deterministic).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterPencilHarvestCap.lean`
(pg-iterate OK 15s; 11 theorems; full axiom lists read manually via `lake env lean`:
all exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx, no new axioms).

## The mechanism (probe, exact)

Why did the census's 3-pencil composites always harvest FEWER than two pencils?
It is a **dimension count**, not a value-collision accident:

* Pencil differences `d_ij = pencil_i − pencil_j` are PAIRS of codewords (deg `< k`)
  vanishing (both rows) on the aligned-overlaps `A_i ∩ A_j`, telescoping
  `d₁₂ + d₂₃ = d₁₃`.  The free parameters live in `V₁₂ × V₂₃` (vanishing spaces)
  subject to `(d₁₂+d₂₃)|_{ov₁₃} = 0`.
* Coverage of `[0,N)` by three `(T−1−t)`-aligned regions forces overlap mass
  `Σ|ov| ≥ 3(T−1−t) − N`; the parameter budget is `2k`.
* **Exact rank computations**: solution dimension `= max(0, 2k − Σ|ov|)` in EVERY
  geometry tried (contiguous/random point sets, balanced/skewed splits, μ_128 and
  μ_256) — the vanishing conditions were never degenerate.
* Consequences: three nearly-fully-aligned pencils are linearly IMPOSSIBLE for
  shortfall `t ≤ 13` at μ_256 (`t ≤ 9` at μ_128), matching the generic threshold
  `⌈(3(T−1)−N−2k+1)/3⌉`.  With TWO full pencils fixed (the census's extremal
  configuration), the third pencil's aligned size caps at exactly `k`
  (affine feasibility: `|ov₁₃|+|ov₂₃| ≤ k`), forcing margin `D = T − k` and a
  **marginal harvest of 2** at both μ scales
  (`ledger: 2(N−T+1) + 2 vs N`, slack used 2 of `2T−N−2`).
* Prize ratios: `3(T−1) − N = 704643071 > 2k = 536870912` — the deficit scales
  (`fully_aligned_triple_dimension_deficit`, kernel).  Generic forced margin next to
  two full pencils: `T − k = 324359510`, marginal harvest `⌊(N−k)/(T−k)⌋ = 2`
  (`forced_margin_arith`, kernel arithmetic).

## Kernel-checked (prize shape)

* `underAligned_riders_mul_le` — margin harvest bound: `A + D ≤ T ⟹
  #riders · D ≤ N − T + D` (from in-tree `riders_card_mul_le`; each rider burns
  `≥ D` disjoint votes).
* `thirdPencil_card_le_of_margin_five` (`≤ 96189372`),
  `extraPencil_card_le_of_margin_nine` (`≤ 53438540`).
* `stall_budget_of_three_pencil_cover` — bad family covered by three pencils, third
  under-aligned by ≥ 5: `#bad ≤ 2·480946859 + 96189372 = 1058083090 ≤ N`.  **The
  `StallResidual` budget holds on this class.**  The needed margin (5) is seven
  orders of magnitude below the probe-measured forced margin (`T−k ≈ 3.2·10⁸`).
* `stall_budget_of_four_pencil_cover` — two arbitrary + two margin-9 pencils:
  `≤ 1068770798 ≤ N` — marginal harvests compound.
* `margin_four_fails` — margin 4 does NOT close the three-pencil ledger
  (`1082130433 > N`): 5 is sharp for this route.
* `ridesAll_of_pencil_subfamily` — reusable BadFamilyData→RidesAll glue.
* Ledger rungs `threePencil_margin_ledger`, `fourPencil_margin_ledger`.

## Honesty — what remains open

1. **The margin hypotheses are the open content.**  The probe pins them at generic
   rank; a kernel proof needs rank-independence of the vanishing conditions on
   adversarial point configurations (none found that defeats it; a BGK/Paley-style
   special geometry — e.g. multiplicative-coset point sets creating low-degree
   Bezout identities `z₁₂ρ + z₂₃σ = z₁₃τ` — is the only imaginable escape).
2. **The compounding does NOT close `StallResidual` entirely**: for m pencils the
   extras need `Σ_j (N−T+D_j)/D_j ≤ 111848106`, i.e. `Σ 1/D_j ≲ 0.2326`; margins
   must grow with pencil count, which is plausible (deficit grows per pencil) but
   unproven.  Also unproven: that every bad family IS covered by few pencils (the
   fiber partition gives through-base pencil covers of unbounded count).
3. No δ* movement; bracket `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

## Next target

Kernel-check the dimension count itself in the cleanest case: linear independence of
evaluation conditions for vanishing-constrained codeword pairs when the three overlap
sets are DISJOINT (no triple points) — there the system `z₁₂ρ + z₂₃σ = z₁₃τ` with
degree budgets `3k − Σ|ov| < k` has only the zero solution by a resultant/degree
argument that may be formalizable; that would convert the three-pencil margin
hypothesis into a theorem for triple-point-free geometries, leaving only the
degenerate-geometry corner.
