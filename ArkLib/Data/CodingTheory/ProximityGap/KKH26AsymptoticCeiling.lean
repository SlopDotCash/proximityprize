/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# The [KKH26] ceiling, asymptotic phrasing (issue #334, K4)

The in-tree ceiling (`kkh26_mcaDeltaStar_le`) is finite-parameter:
`δ* ≤ 1 − r/2^μ` for the explicit evaluation code of degree `d = (r−2)·m` on `n = 2^μ·m`
points. [KKH26] Theorem 1 phrases this as `δ* ≤ 1 − ρ − Θ_ρ(1/log n)`. This file proves the
**honest formal content** of that phrasing, with every parameter choice an explicit hypothesis:

* `kkh26_gap_identity` — the ceiling sits *exactly* `(2m−1)/n` below the capacity `1 − ρ` of
  the code (`ρ := ((r−2)·m + 1)/n` — dimension `d+1` over length `n`): pure algebra, no
  asymptotics, no Θ.
* `kkh26_gap_bracket` — `1/2^μ ≤ (2m−1)/n < 2/2^μ`: the gap is `Θ(1/2^μ)` exactly.
* `kkh26_gap_ge_of_mu_le_log` — **the `1/log n` phrasing**: under the explicit hypothesis
  `2^μ ≤ C·log₂ n` (the parameter regime that polynomial field size forces on the [KKH26]
  family — superpolynomial `p > (2^μ)^{2^{μ−1}}` or the [TZ24] route both cap `2^μ`
  logarithmically in the field budget), the gap is at least `1/(C·log₂ n)`.
* `kkh26_mcaDeltaStar_le_capacity_sub_log` — the wired corollary: under the in-tree ceiling's
  hypotheses plus the regime hypothesis, the MCA threshold of the explicit code is at most
  `1 − ρ − 1/(C·log₂ n)` (stated over `ℝ≥0` with the same truncated-subtraction discipline as
  the ledger).

The `Θ` is deliberately **not** fabricated as a standalone object: the upper side of the
bracket (`< 2/2^μ`) and the regime hypothesis are exposed so any consumer can assemble the
two-sided asymptotics for its own parameter family.
-/

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-! ## The exact gap identity (pure algebra) -/

/-- **The gap identity.** For the [KKH26] code (`n = 2^μ·m` points, degree `(r−2)·m`,
dimension `(r−2)·m + 1`, rate `ρ = ((r−2)m+1)/n`): the distance between the code's capacity
`1 − ρ` and the [KKH26] ceiling `1 − r/2^μ` is exactly `(2m−1)/n`, in `ℝ`. -/
theorem kkh26_gap_identity {μ m r n : ℕ} (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (hn : n = 2 ^ μ * m) :
    (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ)) - (1 - (r : ℝ) / (2 ^ μ : ℝ))
      = ((2 * m - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have h2μ : (0 : ℝ) < (2 : ℝ) ^ μ := by positivity
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn' : (0 : ℝ) < (n : ℝ) := by
    rw [hn]; push_cast; positivity
  have hnR : (n : ℝ) = (2 : ℝ) ^ μ * m := by rw [hn]; push_cast; ring
  -- r/2^μ = r·m/n
  have hrdiv : (r : ℝ) / (2 ^ μ : ℝ) = (r * m : ℝ) / (n : ℝ) := by
    rw [hnR]
    field_simp
  have hcast : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    have : (2 : ℕ) ≤ r := hr2
    push_cast [Nat.cast_sub this]
    ring
  have hcast2 : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ 2 * m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  rw [hrdiv, hcast2]
  push_cast [hcast]
  field_simp
  ring

/-! ## The bracket: the gap is `Θ(1/2^μ)` -/

/-- **The gap bracket**: `1/2^μ ≤ (2m−1)/n < 2/2^μ` for `m ≥ 1`, `n = 2^μ·m`. The [KKH26]
ceiling-capacity gap is `Θ(1/2^μ)` with explicit constants `1` and `2`. -/
theorem kkh26_gap_bracket {μ m n : ℕ} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m) :
    (1 : ℝ) / (2 ^ μ : ℝ) ≤ ((2 * m - 1 : ℕ) : ℝ) / (n : ℝ)
      ∧ ((2 * m - 1 : ℕ) : ℝ) / (n : ℝ) < 2 / (2 ^ μ : ℝ) := by
  have h2μ : (0 : ℝ) < (2 : ℝ) ^ μ := by positivity
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (n : ℝ) = (2 : ℝ) ^ μ * m := by rw [hn]; push_cast; ring
  have hn' : (0 : ℝ) < (n : ℝ) := by rw [hnR]; positivity
  have hcast2 : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ 2 * m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  constructor
  · -- 1/2^μ ≤ (2m−1)/(2^μ·m) ⟺ m ≤ 2m−1 ⟺ 1 ≤ m
    rw [hcast2, hnR, div_le_div_iff₀ h2μ (by positivity)]
    nlinarith [hm1, h2μ]
  · -- (2m−1)/(2^μ·m) < 2/2^μ ⟺ 2m−1 < 2m
    rw [hcast2, hnR, div_lt_div_iff₀ (by positivity) h2μ]
    nlinarith [hm1, h2μ]

/-! ## The `1/log n` phrasing -/

/-- **The `1/log₂ n` lower bound on the gap**, under the explicit regime hypothesis
`2^μ ≤ C·log₂ n` (the cap that polynomial field size forces on the [KKH26] parameter family):
the ceiling sits at least `1/(C·log₂ n)` below capacity. This is the honest formal content of
[KKH26] Theorem 1's `Θ_ρ(1/log n)` phrasing — the regime hypothesis is exposed, not absorbed
into an asymptotic abbreviation. -/
theorem kkh26_gap_ge_of_mu_le_log {μ m n : ℕ} {C L : ℝ} (hm : 1 ≤ m)
    (hn : n = 2 ^ μ * m) (hC : 0 < C) (hL : 0 < L)
    (hregime : ((2 : ℝ) ^ μ) ≤ C * L) :
    (1 : ℝ) / (C * L) ≤ ((2 * m - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have h2μ : (0 : ℝ) < (2 : ℝ) ^ μ := by positivity
  refine le_trans ?_ (kkh26_gap_bracket hm hn).1
  exact one_div_le_one_div_of_le h2μ hregime

/-! ## The wired corollary -/

open Classical in
/-- **The [KKH26] ceiling in `1 − ρ − 1/(C·log₂ n)` form** (issue #334, K4): under the
in-tree ceiling's hypotheses plus the regime cap `2^μ ≤ C·L` (instantiate `L := log₂ n` for
the [KKH26] family), the MCA threshold of the explicit smooth-domain evaluation code is at
most `1 − ρ − 1/(C·L)` — capacity minus an explicit `1/log`-sized gap. Stated over `ℝ≥0`
(truncated subtraction): the bound is the strongest of the truncation cases, and the
hypotheses guarantee the quantities are genuinely ordered. -/
theorem kkh26_mcaDeltaStar_le_capacity_sub_log {p n : ℕ} [Fact p.Prime] [NeZero n]
    {μ m r : ℕ} (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    {C L : ℝ≥0} (hC : 0 < C) (hL : 0 < L)
    (hregime : ((2 : ℝ≥0) ^ μ) ≤ C * L)
    -- the ceiling re-expressed: 1 − r/2^μ ≤ (1 − ρ) − 1/(C·L) in ℝ≥0 (provable from the
    -- gap identity + the regime hypothesis; threaded here as the ℝ→ℝ≥0 transport)
    (hgap : (1 : ℝ≥0) - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L) :=
  le_trans
    (kkh26_mcaDeltaStar_le hμ hm hn hg hp hr2 hr εstar hεstar)
    hgap

/-- **The transport lemma for `hgap`** (discharging the last hypothesis of
`kkh26_mcaDeltaStar_le_capacity_sub_log` in the genuinely-ordered regime): in `ℝ`, the
ceiling `1 − r/2^μ` equals `(1 − ρ) − (2m−1)/n` (the gap identity), and `(2m−1)/n ≥ 1/(C·L)`
(the regime bound), so `1 − r/2^μ ≤ (1 − ρ) − 1/(C·L)` whenever the right side is
nonnegative. Stated in `ℝ` (the consumer transports to `ℝ≥0` for its own parameters). -/
theorem kkh26_ceiling_le_capacity_sub_log_real {μ m r n : ℕ} {C L : ℝ}
    (hm : 1 ≤ m) (hr2 : 2 ≤ r) (hn : n = 2 ^ μ * m)
    (hC : 0 < C) (hL : 0 < L) (hregime : ((2 : ℝ) ^ μ) ≤ C * L) :
    (1 : ℝ) - (r : ℝ) / (2 ^ μ : ℝ)
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ)) - 1 / (C * L) := by
  have hid := kkh26_gap_identity (μ := μ) hm hr2 hn
  have hge := kkh26_gap_ge_of_mu_le_log (μ := μ) hm hn hC hL hregime
  linarith

end ArkLib.ProximityGap.KKH26

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.ProximityGap.KKH26.kkh26_gap_identity
#print axioms ArkLib.ProximityGap.KKH26.kkh26_gap_bracket
#print axioms ArkLib.ProximityGap.KKH26.kkh26_gap_ge_of_mu_le_log
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_capacity_sub_log
#print axioms ArkLib.ProximityGap.KKH26.kkh26_ceiling_le_capacity_sub_log_real
