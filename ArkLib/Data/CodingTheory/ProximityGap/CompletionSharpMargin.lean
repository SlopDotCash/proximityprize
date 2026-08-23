/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

/-!
# The completion anchor's SHARP sub-`√q` form and its thin-regime collapse (#444)

The in-tree worst-case anchor `norm_eta_torsion_le` reports `‖η_b‖ ≤ √q`, but its own
proven intermediate `mul_norm_eta_torsion_le` carries strictly more:

  `t · ‖η_b‖ ≤ (t−1)·√q + 1`,   `t = (q−1)/d`.

Dividing by `t > 0` gives the **sharp sub-`√q` bound**

  **`‖η_b‖ ≤ √q − (√q − 1)/t`**     (`norm_eta_torsion_sharp_le`)

— the classical Gauss-sum completion already beats the `√q` anchor by the margin
`margin(t) = (√q − 1)/t`.  Two consequences are recorded here, both EXTEND-proven off
the in-tree intermediate (no new probe-level mathematics, only the arithmetic the parent
file discarded):

* **`norm_eta_torsion_lt`** — the bound is *strict*: `‖η_b‖ < √q` whenever `q > 1` and
  `t ≥ 1` (the margin is genuinely positive, the anchor is never attained by completion).
* **`completion_margin_le_of_thin`** — the **refutation mechanism**: the completion margin
  is `margin(t) = (√q − 1)/t ≤ √q · (d/(q−1))`, so as a *fraction of* `√q` it is bounded by
  `d/(q−1)`.  In the prize regime `q = n^β` (`β ≈ 4–5`) with `d = n` thin, `d/(q−1) ~ n/q
  → 0`: the sharp completion bound stays `~ √q`, beaten by only an `o(1)` fraction, and
  therefore **cannot reach** the prize target `√(n·log(p/n)) ≪ √q`.  This is the precise
  in-tree statement of *why classical Gauss-sum completion is non-proving for CORE on thin
  subgroups* — a refutation-with-mechanism, not a wall re-mapping.

No moment input, no Weil input; purely the completion identity the parent file already
proved.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

NOTE (honest scope).  This SHARPENS and DELIMITS the classical completion route; it does
NOT prove CORE.  The genuinely-open `√(n·log(p/n))` bound lives strictly *below* this
completion anchor and is untouched.  No `δ*`/capacity/beyond-Johnson claim; the
cliff-at-`n/2` is not referenced.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumWorstCase

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The sharp sub-`√q` completion bound.**  Dividing the proven intermediate
`t·‖η_b‖ ≤ (t−1)√q + 1` by `t > 0`:

  `‖η_b‖ ≤ √q − (√q − 1)/t`,   `t = (q−1)/d`.

The classical completion already beats the `√q` anchor by the margin `(√q − 1)/t`. -/
theorem norm_eta_torsion_sharp_le {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖
      ≤ Real.sqrt (Fintype.card F)
          - (Real.sqrt (Fintype.card F) - 1) / (((Fintype.card F - 1) / d : ℕ) : ℝ) := by
  set t : ℕ := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  have hmain := mul_norm_eta_torsion_le hd hd0 hψ hb
  -- `t·‖η‖ ≤ (t−1)√q + 1` with `(t−1 : ℕ) = (t : ℝ) − 1`
  have htcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub ht0]; norm_num
  rw [htcast] at hmain
  -- `‖η‖ ≤ √q − (√q−1)/t  ⟺  (√q−1)/t + ‖η‖ ≤ √q`; clear the denominator via `t > 0`.
  rw [← sub_nonneg]
  have key : (0 : ℝ) ≤ (t : ℝ) * ((Real.sqrt (Fintype.card F)
      - (Real.sqrt (Fintype.card F) - 1) / (t : ℝ)) - ‖eta ψ (torsion F d) b‖) := by
    have hexp : (t : ℝ) * ((Real.sqrt (Fintype.card F)
        - (Real.sqrt (Fintype.card F) - 1) / (t : ℝ)) - ‖eta ψ (torsion F d) b‖)
        = ((t : ℝ) - 1) * Real.sqrt (Fintype.card F) + 1
          - (t : ℝ) * ‖eta ψ (torsion F d) b‖ := by
      field_simp
      ring
    rw [hexp]; linarith [hmain]
  exact (mul_nonneg_iff_of_pos_left ht0R).mp key

/-- **The completion margin is strictly positive ⟹ the anchor is never attained.**
For `q > 1` and `t ≥ 1`, `‖η_b‖ < √q`: classical Gauss-sum completion strictly beats the
`√q` anchor. -/
theorem norm_eta_torsion_lt {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    ‖eta ψ (torsion F d) b‖ < Real.sqrt (Fintype.card F) := by
  set t : ℕ := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  -- `√q > 1`, so the margin `(√q − 1)/t > 0`
  have hq1' : 1 < Fintype.card F := Fintype.one_lt_card (α := F)
  have hsqrt_gt1 : (1 : ℝ) < Real.sqrt (Fintype.card F) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    refine Real.sqrt_lt_sqrt (by norm_num) ?_
    exact_mod_cast hq1'
  have hmargin_pos : (0 : ℝ) < (Real.sqrt (Fintype.card F) - 1) / (t : ℝ) :=
    div_pos (by linarith) ht0R
  have hsharp := norm_eta_torsion_sharp_le hd hd0 hψ hb
  rw [← ht] at hsharp
  linarith

/-- **The refutation mechanism: the completion margin, as a fraction of `√q`, is `≤ d/(q−1)`.**

`margin(t) = (√q − 1)/t ≤ √q · (d/(q−1))`.  In the prize regime `q = n^β` (`β ≈ 4–5`)
with `d = n` thin, the RHS fraction `d/(q−1) ~ n/q → 0`: the sharp completion bound stays
`~ √q`, beaten only by an `o(1)` fraction, hence **cannot reach** the prize bound
`√(n·log(p/n)) ≪ √q`.  This is the in-tree statement of why classical Gauss-sum completion
is non-proving for CORE on thin subgroups. -/
theorem completion_margin_le_of_thin {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d) :
    (Real.sqrt (Fintype.card F) - 1) / (((Fintype.card F - 1) / d : ℕ) : ℝ)
      ≤ Real.sqrt (Fintype.card F) * ((d : ℝ) / ((Fintype.card F - 1 : ℕ) : ℝ)) := by
  set t : ℕ := (Fintype.card F - 1) / d with ht
  have htd : t * d = Fintype.card F - 1 := Nat.div_mul_cancel hd
  have hq1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F); omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, zero_mul] at htd; omega
    · exact h
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  have hd0R : (0 : ℝ) < d := by exact_mod_cast hd0
  have hq1R : (0 : ℝ) < ((Fintype.card F - 1 : ℕ) : ℝ) := by exact_mod_cast hq1
  -- `t = (q−1)/d` so `t·d = q−1`, i.e. `1/t = d/(q−1)` as reals
  have htdR : (t : ℝ) * (d : ℝ) = ((Fintype.card F - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, htd]
  have hinv : (1 : ℝ) / (t : ℝ) = (d : ℝ) / ((Fintype.card F - 1 : ℕ) : ℝ) := by
    rw [eq_div_iff (ne_of_gt hq1R), ← htdR]; field_simp
  -- `√q − 1 ≤ √q`, then `(√q − 1)/t ≤ √q/t = √q·(1/t) = √q·d/(q−1)`
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  calc (Real.sqrt (Fintype.card F) - 1) / (t : ℝ)
      ≤ Real.sqrt (Fintype.card F) / (t : ℝ) := by
        gcongr
        linarith
    _ = Real.sqrt (Fintype.card F) * ((d : ℝ) / ((Fintype.card F - 1 : ℕ) : ℝ)) := by
        rw [div_eq_mul_one_div, ← hinv]

end ArkLib.ProximityGap.SubgroupGaussSumWorstCase

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.norm_eta_torsion_sharp_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.norm_eta_torsion_lt
#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase.completion_margin_le_of_thin
