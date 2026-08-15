# SYZ9: the degenerate-channel rank wall — DONE (2026-07-10)

Status: **LANDED, axiom-clean.** Formalizes item (2) of the SYZ7 strip map §6 (the ceiling-side
barrier). File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ9ChannelRankWall.lean`.
Issue #466 / #507. Tag SYZ9.

## What is proved

The degenerate-subset channel (SYZ1 probe → SYZ2 `mcaEvent_pencil` → SYZ3 witness → SYZ4/SYZ6
ceilings) **provably cannot kill any radius below `(1−ρ)/(2−ρ)`**. Abstracted to SYZ5's altitude
(pure `ℕ`/`ℚ`; the `mcaEvent` side is already discharged by `_G87McaEventSyndromeBridge`), a
channel configuration is `D` threshold-`t` subsets on `n` points, code dimension `k`, each donating
up to `n−t` bad scalars. Two structural facts pin the radius:

- **rank / plantability budget** (`_G86RankCollapseDichotomy.plantable_generic_cap`, SYZ4 doubling
  convention `2(t−k)D < 2(n−k)`): `D·(t−k) < n−k`;
- **budget beat** (`ε*·q ≈ B`): `B < D·(n−t)`.

With `R = n−k`, `m = t−k`, `c = n−t` (so `R = m+c`), eliminating `D` gives the **master inequality**
`m·B < R·c`, i.e. `(t−k)·B < (n−k)·(n−t)` — *free of `D`* (the elimination is exactly the
continuous minimisation `min_D max(B/D, R(1−1/D)) = R·B/(R+B)`, so it is automatically the
worst-`D` optimum). Radius form: `(n−k)·B < (n−t)·((n−k)+B)`. At `B = n`:
`(n−t)·(2n−k) > (n−k)·n`, i.e. **`δ > (n−k)/(2n−k) = (1−ρ)/(2−ρ)`, strict, no `o(1)`.**

The `o(1)` of the informal statement is only `B` vs exactly `n` plus the integer lattice; the
algebraic core is a clean strict inequality.

## Theorems (verbatim signatures)

- `channel_master_abstract {R m c D B : ℕ} (hR : R = m + c) (hcpos : 0 < c)
  (hplant : D * m < R) (hbudget : B < D * c) : m * B < R * c`
- `channel_master {n k t D B : ℕ} (hkt : k ≤ t) (hc : t < n)
  (hplant : D * (t - k) < n - k) (hbudget : B < D * (n - t)) :
  (t - k) * B < (n - k) * (n - t)`
- `channel_radius_form … : (n - k) * B < (n - t) * ((n - k) + B)`
- `channel_radius_infimum_Beq_n … (hbudget : n < D * (n - t)) :
  (n - k) * n < (n - t) * (2 * n - k)`
- `infimum_ratio_eq {n k : ℕ} (hkn : k < n) :
  ((n:ℚ) - k) / (2 * n - k) = (1 - (k:ℚ)/n) / (2 - (k:ℚ)/n)`
- `channel_radius_gt_infimum … : (1 - (k:ℚ)/n) / (2 - (k:ℚ)/n) < ((n:ℚ) - t) / n`  ← the δ > (1−ρ)/(2−ρ) wall
- `production_channel_safe {t D : ℕ} (hkt : 536870912 ≤ t) (hc : t < 1073741824)
  (hplant : D * (t - 536870912) < 536870912)
  (hbudget : 1073741824 < D * (1073741824 - t)) : 357913941 < 1073741824 - t`
- `production_safe_radius_lt_third : (357913941:ℚ)/2^30 < 1/3 ∧ (1:ℚ)/3 < 357913942/2^30`
- `rateQuarter_realD_infimum : ((1073741824:ℚ) - 268435456)/(2*1073741824 - 268435456) = 3/7`
- `rateQuarter_integer_lift : (3:ℚ)/7 < 1/2`
- `channel_reach_bracket : (357913941:ℚ)/2^30 < 358612991/2^30 ∧
  (357913941:ℚ)/2^30 < 1/3 ∧ (1:ℚ)/3 < 358612991/2^30`

## Production reach (rate 1/2, `n=2^30`, `k=2^29`, `B=2^30`)

Complement `c = n−t > 357913941 = ⌊2^30/3⌋` (so `c ≥ 357913942`). **The channel cannot kill any
radius `≤ 357913941/2^30` (`< 1/3`); its first killable lattice radius is `357913942/2^30 > 1/3`.**
Combined with SYZ6's ceiling `358612991/2^30 ≈ 0.33399`, the channel's exact reach is the lattice
radii in `(357913941/2^30, 358612991/2^30] ⊆ (1/3, 1]`.

## Rate 1/4 (ties to SYZ5)

Real-`D` infimum `(1−ρ)/(2−ρ) = 3/7 ≈ 0.4286`; SYZ5's integer-`D` refinement lifts this to `1/2`
(crossing `D* = 7/3` non-integral). `3/7 < 1/2` recorded.

## Axiom audit

All theorems: `[propext, Classical.choice, Quot.sound]` (standard clean set). No `sorry`,
no new axioms. Type-checks via `scripts/pg-iterate.sh` (~5s; imports Mathlib only, so no
missing-olean issues).

## Honest scope / gaps

Bars **one construction family**: per-subset degenerate pencils with *independent* rank accounting
(the object SYZ2's `mcaEvent_pencil` route feeds to `mcaDeltaStar_le_of_bad`). Does **not** prove
the decisive strip `(Johnson, 1/3)` is good — a non-degenerate-subset construction remains
logically possible. The SYZ7 scan (`probe_syz7_strip_scan.py`) found none, but that is search
evidence, not a proof. What is proven: *the channel starves below `(1−ρ)/(2−ρ)`.* This isolates
`[Johnson, 1/3]` as "genuinely-new-construction-required" (SYZ7 §6 item 3 still open both ways).

## SYZ7 map update

SYZ7 §6 **item (2) → DONE** (this file). Items (1) `CellPackageSupply` floor jump and (3)
strip decision remain open.

## Cross-references

- SYZ arc: `_SYZ5RateQuarterChannelCeiling.lean` (arithmetic pattern mirrored here),
  `_SYZ4DegenerateChannelCeiling.lean`, `_SYZ6FinerGradingCeiling.lean` (upper ceiling
  `358612991/2^30`).
- Rank machinery: `_G86RankCollapseDichotomy.lean` (`plantable_generic_cap`),
  `_G87McaEventSyndromeBridge.lean`.
- Map: `docs/kb/deltastar-466-syz7-strip-map-2026-07-10.md`.
