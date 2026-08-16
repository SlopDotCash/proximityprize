/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Round 9 (Issue #232, ABF26) — the subgroup Gauss-sum SECOND MOMENT, exactly, with NO Weil bound.

Rounds 7–8 reduced the prize-deciding question to the magnitude of the **subgroup-restricted** Gauss
sum `η_b := ∑_{y∈G} ψ(b·y)` (`G` = the smooth `2^k`-subgroup), and proved that a clean *per-frequency*
`√q` bound needs Weil's theorem for curves, which Mathlib lacks. This file supplies the one piece that
is **fully provable elementarily** — the **second moment** of the subgroup Gauss sum over all
frequencies, via additive-character orthogonality (Parseval), with **no Weil input**:

> `subgroup_gaussSum_secondMoment`:  `∑_{b∈F} ‖∑_{y∈G} ψ(b·y)‖² = q·|G|`.

Consequences (the genuine analytic content for the M2 / collision question):
* `subgroup_gaussSum_l2_average`: the **average** of `‖η_b‖²` over the `q` frequencies is exactly
  `|G|`. So the *typical* subgroup Gauss sum has size `√|G|`, **not** `√q` — i.e. on average the
  subgroup character sum is far smaller than a full-field Gauss sum. This is the average-case
  cancellation the collision-count second moment `M2` runs on; only the *worst-case* per-`b` bound
  (which `√|G|`-on-average does not give) needs Weil.
* `exists_frequency_gaussSum_sq_ge`: pigeonhole — some frequency `b` has `‖η_b‖² ≥ |G|`, so the
  average scale `√|G|` is genuinely attained (not all terms lie below it).

This is an honest partial result: it controls the subgroup Gauss sum in `L²`/average, which is exactly
the regime that decides anti-concentration of `M2` on average, while leaving the per-frequency worst
case (the deep-interior pin) open. All `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The subgroup Gauss sum at frequency `b`: `η_b = ∑_{y∈G} ψ(b·y)`. -/
noncomputable def eta (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℂ := ∑ y ∈ G, ψ (b * y)

/-- **The subgroup Gauss-sum second moment, exactly: `∑_b ‖η_b‖² = q·|G|`.** No Weil bound — pure
additive-character orthogonality (`AddChar.sum_mulShift`): expanding `‖η_b‖² = η_b · conj η_b` into a
double sum over `(y, y') ∈ G × G` and summing over `b` collapses each pair to `q·[y = y']`. -/
theorem subgroup_gaussSum_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  -- Work with the complex identity `∑_b η_b · conj η_b = q·|G|`, then read off `‖η_b‖²`.
  -- Step 1: each `η_b · conj η_b` is `‖η_b‖²` (RCLike.mul_conj).
  have hnorm : ∀ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b; rw [RCLike.mul_conj]; norm_cast
  -- Step 2: expand `η_b · conj η_b` and sum over `b`, collapsing via orthogonality.
  have hcomplex : (∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G b))
      = (Fintype.card F : ℂ) * G.card := by
    -- conj of a value: `conj (ψ a) = ψ⁻¹ a = ψ (-a)`
    have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
      intro a
      rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
    calc ∑ b : F, eta ψ G b * (starRingEnd ℂ) (eta ψ G b)
        = ∑ b : F, ∑ y' ∈ G, ∑ y ∈ G, ψ (b * (y' - y)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
            rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
          have hL : eta ψ G b = ∑ y ∈ G, ψ (b * y) := rfl
          rw [hconjeta, hL, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun y' _ => ?_)
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have harg : b * y' + -(b * y) = b * (y' - y) := by ring
          rw [← AddChar.map_add_eq_mul, harg]
      _ = ∑ y' ∈ G, ∑ y ∈ G, ∑ b : F, ψ (b * (y' - y)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y' _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ y' ∈ G, ∑ y ∈ G, (if y' = y then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun y' _ => ?_)
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [AddChar.sum_mulShift (y' - y) hψ]
          simp [sub_eq_zero]
      _ = ∑ y' ∈ G, (Fintype.card F : ℂ) := by
          refine Finset.sum_congr rfl (fun y' hy' => ?_)
          rw [Finset.sum_ite_eq G y' (fun _ => (Fintype.card F : ℂ))]
          simp [hy']
      _ = (Fintype.card F : ℂ) * G.card := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Step 3: cast the complex identity back to the real second moment.
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = (Fintype.card F : ℂ) * G.card := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => (hnorm b).symm)
  have hreal : ((∑ b : F, ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = (((Fintype.card F : ℝ) * G.card : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **The `L²`-average of the subgroup Gauss sum is exactly `|G|`.** Dividing the second moment by the
number of frequencies `q = |F|`: the average of `‖η_b‖²` over all `b ∈ F` is `|G|`, so the *typical*
subgroup Gauss sum has size `√|G|` — far below the full-field `√q` (since `|G| ≤ q`). This is the
average-case cancellation; the per-frequency worst case (the deep-interior pin) still needs Weil. -/
theorem subgroup_gaussSum_l2_average {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (∑ b : F, ‖eta ψ G b‖ ^ 2) / (Fintype.card F : ℝ) = G.card := by
  rw [subgroup_gaussSum_secondMoment hψ G, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast hq.ne'), mul_one]

/-- **Some frequency attains the average: `∃ b, ‖η_b‖² ≥ |G|`.** Not all `q` terms can lie strictly
below the average `|G|`, else their sum would be `< q·|G|`, contradicting the exact second moment. (The
trivial witness is `b = 0`, where `η_0 = |G|` so `‖η_0‖² = |G|²`; the content is that the second moment
is *attained*, pinning the average scale at `√|G|`.) -/
theorem exists_frequency_gaussSum_sq_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    ∃ b : F, (G.card : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := by
  by_contra h
  push_neg at h
  have hsum : ∑ b : F, ‖eta ψ G b‖ ^ 2 < ∑ _b : F, (G.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hq))
      (fun b _ => h b)
  rw [subgroup_gaussSum_secondMoment hψ G, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm] at hsum
  exact lt_irrefl _ hsum

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.subgroup_gaussSum_secondMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.subgroup_gaussSum_l2_average
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_frequency_gaussSum_sq_ge
