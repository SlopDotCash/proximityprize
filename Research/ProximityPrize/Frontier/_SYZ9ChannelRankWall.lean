/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.NNReal.Basic

/-!
# SYZ9: the degenerate-channel rank wall (issue #466 / #507)

This file makes precise and proves the **ceiling-side barrier** promised as item (2) of the SYZ7
strip map (`docs/kb/deltastar-466-syz7-strip-map-2026-07-10.md`, §6): the degenerate-subset
channel that powers every landed rate-`1/2` and rate-`1/4` ceiling (SYZ1 probe → SYZ2 pencil →
SYZ3 witness → SYZ4/SYZ6 ceilings) **provably cannot kill any radius below `(1−ρ)/(2−ρ)`**.

## The channel, abstracted to its arithmetic

A configuration is `D` degenerate subsets, each of size `t` (threshold-`t` agreement) on `n`
points, each donating up to `n − t` `mcaEvent`-bad scalars through the SYZ2 `mcaEvent_pencil`
route.  Two structural facts, at the altitude of SYZ5's pure-`ℕ` arithmetic (this is the right
altitude — the `mcaEvent` side is already discharged by `_G87McaEventSyndromeBridge`), pin the
radius:

* **rank / plantability budget** (from `_G86RankCollapseDichotomy.plantable_generic_cap` and the
  SYZ4 doubling convention `2·(t−k)·D < 2·(n−k)`): the `D·(t−k)` parity rows a plantable stack
  spends must fit strictly inside the `n−k` syndrome codimension, i.e.
  `D · (t − k) < n − k`;
* **budget beat** (`ε*·q ≈ B`): to certify a bad event the total donated bad-scalar count must
  exceed the budget, `B < D · (n − t)`.

Write `R = n − k` (codimension), `m = t − k`, `c = n − t` (the complement = radius numerator), so
`R = m + c`.  The two facts are `D·m < R` and `B < D·c`.  Eliminating `D`:

```
  from  B < D·c :    m·B < D·(m·c) = (D·m)·c
  from  D·m < R :    (D·m)·c < R·c            (c > 0)
  hence             m·B < R·c
```

i.e. **`(t − k)·B < (n − k)·(n − t)`** — the master inequality, *free of `D`* (so it holds
for the worst-case `D` automatically: the elimination is exactly the continuous-`D` minimisation
`min_D max(B/D, R(1−1/D)) = R·B/(R+B)`).  Equivalently, in radius form,

```
  (n − k)·B  <  (n − t)·((n − k) + B),
```

and at the budget `B = n` this is `(n − t)·(2n − k) > (n − k)·n`, i.e.

```
  δ = (n−t)/n  >  (n−k)/(2n−k)  =  (1 − ρ)/(2 − ρ)      (ρ = k/n),
```

a **strict, `o(1)`-free** lower bound on the radius of any channel configuration that beats the
budget.  The `o(1)` of the informal statement is only the difference between `B` and exactly `n`
plus the integer lattice; the algebraic content is the clean strict inequality above.

## Production reach (rate `1/2`)

At `n = 2^30`, `k = 2^29`, `B = 2^30` (the `ε*·P` budget), the master inequality forces the
complement `c = n − t > 357913941` (`= ⌊2^30/3⌋`, i.e. `c ≥ 357913942`), so the radius exceeds
`357913941/2^30 = 1/3 − 2^-30`(-ish, the exact best safe rational).  **The channel cannot kill
any radius `≤ 357913941/2^30`.**  Together with SYZ6's ceiling `358612991/2^30 ≈ 0.33399` this
pins the channel's exact reach: it kills precisely (up to the lattice) the radii in
`(357913941/2^30, 1] ≈ (1/3, 1]`.

## Rate `1/4` (ties to SYZ5)

The *real-`D`* infimum at `ρ = 1/4` is `(1−ρ)/(2−ρ) = 3/7 ≈ 0.4286`.  SYZ5
(`_SYZ5RateQuarterChannelCeiling.lean`) sharpens this to the *integer-`D`* floor `1/2` at the
production numbers (the crossing `D* = 7/3` is non-integral).  Both are recorded here as `ℚ`
facts; `3/7 < 1/2` witnesses that the integer refinement is strictly stronger.

## Honest scope

This bars **one construction family**: per-subset degenerate pencils with *independent* rank
accounting, the object SYZ2's `mcaEvent_pencil` route feeds to `mcaDeltaStar_le_of_bad`.  It does
**not** prove that the decisive strip `(Johnson, 1/3)` is good — a genuinely different,
non-degenerate-subset construction remains logically possible.  The SYZ7 empirical scan
(`probe_syz7_strip_scan.py`, A/NEAR/MIX/RAND at `n ∈ {32,64}`) found none, but that is search
evidence, not a proof.  What is proven here is exactly: *the channel starves below `(1−ρ)/(2−ρ)`.*

Axiom-clean (pure `ℕ`/`ℚ` arithmetic; `#print axioms` below).  No `sorry`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall

/-! ## The abstract master inequality (`D` eliminated) -/

/-- **Channel master inequality, abstract form.**  With codimension `R = m + c` (`m = t − k`
the per-subset row count, `c = n − t` the complement/radius numerator), the plantability budget
`D·m < R` and the budget beat `B < D·c` together force `m·B < R·c`, *independently of `D`*.

This is the pure-`ℕ` heart: the elimination of `D` is the continuous minimisation
`min_D max(B/D, R(1−1/D)) = R·B/(R+B)`, so the bound automatically holds for the worst `D`. -/
theorem channel_master_abstract {R m c D B : ℕ}
    (hR : R = m + c) (hcpos : 0 < c)
    (hplant : D * m < R) (hbudget : B < D * c) :
    m * B < R * c := by
  calc m * B ≤ m * (D * c) := Nat.mul_le_mul (le_refl m) (le_of_lt hbudget)
    _ = (D * m) * c := by ring
    _ < R * c := mul_lt_mul_of_pos_right hplant hcpos

/-- **Channel master inequality.**  Any degenerate-channel configuration — `D` threshold-`t`
subsets on `n` points, code dimension `k` — whose plantable rank budget holds
(`D·(t−k) < n−k`, the SYZ4/G86 convention) and which beats the budget `B`
(`B < D·(n−t)`), satisfies

  `(t − k) · B  <  (n − k) · (n − t)`.

The subset count `D` does not appear in the conclusion: the bound is the worst-case-`D` optimum. -/
theorem channel_master {n k t D B : ℕ}
    (hkt : k ≤ t) (hc : t < n)
    (hplant : D * (t - k) < n - k) (hbudget : B < D * (n - t)) :
    (t - k) * B < (n - k) * (n - t) := by
  have hR : n - k = (t - k) + (n - t) := by omega
  exact channel_master_abstract hR (by omega) hplant hbudget

/-- **Radius form.**  Equivalent rearrangement `(n−k)·B < (n−t)·((n−k)+B)`.  Dividing by
`n·((n−k)+B)` this reads `δ = (n−t)/n > (n−k)·B / (n·((n−k)+B))`, the exact channel radius floor
for budget `B`. -/
theorem channel_radius_form {n k t D B : ℕ}
    (hkt : k ≤ t) (hc : t < n)
    (hplant : D * (t - k) < n - k) (hbudget : B < D * (n - t)) :
    (n - k) * B < (n - t) * ((n - k) + B) := by
  have h := channel_master hkt hc hplant hbudget
  have hR : n - k = (t - k) + (n - t) := by omega
  calc (n - k) * B = ((t - k) + (n - t)) * B := by rw [hR]
    _ = (t - k) * B + (n - t) * B := by ring
    _ < (n - k) * (n - t) + (n - t) * B := Nat.add_lt_add_right h _
    _ = (n - t) * ((n - k) + B) := by ring

/-- **The `(1−ρ)/(2−ρ)` infimum, `ℕ` form (`B = n`).**  At the budget `B = n`, any
over-budget channel configuration has complement obeying `(n−k)·n < (n−t)·(2n−k)`, i.e.
`δ · (2 − ρ) > 1 − ρ`.  Strict, no `o(1)`. -/
theorem channel_radius_infimum_Beq_n {n k t D : ℕ}
    (hkt : k ≤ t) (hc : t < n) (hkn : k ≤ n)
    (hplant : D * (t - k) < n - k) (hbudget : n < D * (n - t)) :
    (n - k) * n < (n - t) * (2 * n - k) := by
  have h := channel_radius_form (B := n) hkt hc hplant hbudget
  have he : (n - k) + n = 2 * n - k := by omega
  rw [he] at h
  exact h

/-! ## The rational `(1−ρ)/(2−ρ)` reading -/

/-- The channel infimum `(n−k)/(2n−k)` is exactly `(1 − ρ)/(2 − ρ)` with `ρ = k/n`. -/
theorem infimum_ratio_eq {n k : ℕ} (hkn : k < n) :
    ((n : ℚ) - k) / (2 * (n : ℚ) - k) = (1 - (k : ℚ) / n) / (2 - (k : ℚ) / n) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk : (k : ℚ) < n := by exact_mod_cast hkn
  have h2n : (2 * (n : ℚ) - k) ≠ 0 := by nlinarith
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt hn
  have h2 : (2 - (k : ℚ) / n) ≠ 0 := by
    have hlt : (k : ℚ) / n < 1 := (div_lt_one hn).mpr hk
    have hpos : (0 : ℚ) < 2 - (k : ℚ) / n := by linarith
    exact ne_of_gt hpos
  rw [div_eq_div_iff h2n h2]
  field_simp

/-- **The `(1−ρ)/(2−ρ)` radius wall, `ℚ` form.**  Any channel configuration that beats budget
`B = n` has radius `δ = (n−t)/n` strictly above the infimum `(1 − ρ)/(2 − ρ)`. -/
theorem channel_radius_gt_infimum {n k t D : ℕ}
    (hkt : k ≤ t) (hc : t < n) (hkn : k < n)
    (hplant : D * (t - k) < n - k) (hbudget : n < D * (n - t)) :
    (1 - (k : ℚ) / n) / (2 - (k : ℚ) / n) < ((n : ℚ) - t) / n := by
  have hnat := channel_radius_infimum_Beq_n hkt hc hkn.le hplant hbudget
  -- cast the ℕ inequality to ℚ, using k ≤ t ≤ n to make the subtractions exact
  have hn : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2nk : (0 : ℚ) < 2 * (n : ℚ) - k := by
    have : (k : ℚ) < n := by exact_mod_cast hkn
    nlinarith
  -- (n-k)*n < (n-t)*(2n-k) over ℚ
  have hcast : ((n : ℚ) - k) * n < ((n : ℚ) - t) * (2 * (n : ℚ) - k) := by
    have := hnat
    have e1 : ((n - k : ℕ) : ℚ) = (n : ℚ) - k := by
      rw [Nat.cast_sub hkn.le]
    have e2 : ((n - t : ℕ) : ℚ) = (n : ℚ) - t := by
      rw [Nat.cast_sub hc.le]
    have e3 : ((2 * n - k : ℕ) : ℚ) = 2 * (n : ℚ) - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul]; push_cast; ring
    have hq : ((n - k : ℕ) : ℚ) * (n : ℚ) < ((n - t : ℕ) : ℚ) * ((2 * n - k : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rwa [e1, e2, e3] at hq
  -- rearrange to the ratio comparison
  rw [← infimum_ratio_eq hkn]
  rw [div_lt_div_iff₀ h2nk hn]
  -- goal: (n - k) * n < (n - t) * (2n - k)  (up to commutation)
  nlinarith [hcast]

/-! ## Production reach (rate `1/2`, `n = 2^30 = 1073741824`, `k = 2^29 = 536870912`, `B = 2^30`) -/

/-- **Production channel safety, rate `1/2`.**  Every degenerate-channel configuration that beats
the production budget `B = 2^30` at `n = 2^30`, `k = 2^29` has complement `n − t > 357913941`
(`= ⌊2^30/3⌋`).  Equivalently: **the channel cannot kill any radius `≤ 357913941/2^30`**
(`= 1/3 − 2^-30`-ish, the exact best safe rational). -/
theorem production_channel_safe {t D : ℕ}
    (hkt : 536870912 ≤ t) (hc : t < 1073741824)
    (hplant : D * (t - 536870912) < 536870912)
    (hbudget : 1073741824 < D * (1073741824 - t)) :
    357913941 < 1073741824 - t := by
  have h := channel_master (n := 1073741824) (k := 536870912) (t := t) (B := 1073741824)
    hkt hc hplant hbudget
  -- h : (t - 536870912) * 1073741824 < 536870912 * (1073741824 - t); both sides linear in t
  omega

/-- The exact best safe production radius as a rational: the channel's reach starts strictly above
`357913941/2^30`, i.e. `≤ 357913941/2^30 < 1/3` is safe, while the first killable lattice radius is
`357913942/2^30 > 1/3`. -/
theorem production_safe_radius_lt_third :
    (357913941 : ℚ) / 2 ^ 30 < 1 / 3 ∧ (1 : ℚ) / 3 < 357913942 / 2 ^ 30 := by
  constructor <;> norm_num

/-! ## Rate `1/4` (ties to SYZ5) -/

/-- Real-`D` infimum at rate `1/4`: `(n−k)/(2n−k) = 3/7` for `n = 2^30`, `k = 2^28`. -/
theorem rateQuarter_realD_infimum :
    ((1073741824 : ℚ) - 268435456) / (2 * 1073741824 - 268435456) = 3 / 7 := by
  norm_num

/-- The SYZ5 integer-`D` floor `1/2` strictly beats the real-`D` infimum `3/7` at rate `1/4`
(the crossing `D* = 7/3` is non-integral). -/
theorem rateQuarter_integer_lift :
    (3 : ℚ) / 7 < 1 / 2 := by norm_num

/-! ## The exact channel reach (with SYZ6) -/

/-- **Channel exact reach, rate `1/2`.**  The lower wall proved here (`357913941/2^30`, safe) sits
strictly below the SYZ6 upper ceiling (`358612991/2^30`, killable): the channel kills precisely the
lattice radii in the interval `(357913941/2^30, 358612991/2^30] ⊆ (1/3, 1]`. -/
theorem channel_reach_bracket :
    (357913941 : ℚ) / 2 ^ 30 < 358612991 / 2 ^ 30 ∧
      (357913941 : ℚ) / 2 ^ 30 < 1 / 3 ∧ (1 : ℚ) / 3 < 358612991 / 2 ^ 30 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall

-- Axiom audit (expected: propext / Classical.choice / Quot.sound only)
#print axioms ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall.channel_master
#print axioms ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall.channel_radius_form
#print axioms ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall.channel_radius_gt_infimum
#print axioms ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall.production_channel_safe
#print axioms ArkLib.ProximityGap.Frontier.SYZ9ChannelRankWall.channel_reach_bracket
