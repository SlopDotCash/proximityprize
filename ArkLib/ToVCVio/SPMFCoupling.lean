/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio

/-!
# Identical-until-bad coupling for possibly-failing SPMF games

VCVio's `tvDist_le_probEvent_of_probOutput_eq_of_not` requires both games to be `NeverFail`.
The CO25 §5.8 hybrid games return `SPMF (Option …)` and *can* fail (the `pure none` abort
branches), so that lemma does not apply directly. This file proves the strictly more general
**failing-game** version: if two SPMF games

* agree on the output probability of every non-bad outcome (`h_eq`),
* have equal bad-event probability (`h_bad`), and
* have equal failure mass (`h_fail`),

then their total-variation distance is at most the bad-event probability. This is the reusable
coupling foundation for every CO25 §5.6→§5.8 hybrid step (Claims 5.21–5.24), where the games
differ only off the §5.6 bad event `E`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open scoped ENNReal NNReal

namespace SPMF

variable {α : Type}

/-- **Identical-until-bad, failing-game form.** If two `SPMF` games agree on every non-bad
output probability, have equal bad-event probability, and equal failure mass, then their TV
distance is bounded by the bad-event probability. Generalizes VCVio's `NeverFail` version. -/
theorem tvDist_le_probEvent_of_identicalOffBad
    (p q : SPMF α) (b : α → Prop)
    (h_eq : ∀ x, ¬ b x → Pr[= x | p] = Pr[= x | q])
    (h_bad : Pr[ b | p] = Pr[ b | q])
    (h_fail : p.toPMF none = q.toPMF none) :
    SPMF.tvDist p q ≤ Pr[ b | p].toReal := by
  classical
  rw [SPMF.tvDist, PMF.tvDist]
  refine ENNReal.toReal_mono probEvent_ne_top ?_
  rw [PMF.etvDist, tsum_option _ ENNReal.summable]
  have hfail0 : ENNReal.absDiff (p.toPMF none) (q.toPMF none) = 0 := by
    rw [h_fail, ENNReal.absDiff_self]
  have hsum : (∑' x, ENNReal.absDiff (p.toPMF (some x)) (q.toPMF (some x)))
      = ∑' x, ENNReal.absDiff (Pr[= x | p]) (Pr[= x | q]) := by
    refine tsum_congr fun x => ?_
    simp [probOutput_def, SPMF.apply_eq_toPMF_some]
  rw [hfail0, zero_add, hsum]
  calc
    (∑' x, ENNReal.absDiff (Pr[= x | p]) (Pr[= x | q])) / 2
        ≤ (∑' x, if b x then (Pr[= x | p] + Pr[= x | q]) else 0) / 2 :=
          ENNReal.div_le_div_right
            (ENNReal.tsum_le_tsum fun x => by
              by_cases hx : b x
              · simpa [hx] using ENNReal.absDiff_le_add (Pr[= x | p]) (Pr[= x | q])
              · simp [hx, h_eq x hx, ENNReal.absDiff_self]) _
    _ = (Pr[ b | p] + Pr[ b | q]) / 2 := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
        congr 1
        calc
          (∑' x, if b x then (Pr[= x | p] + Pr[= x | q]) else 0)
              = (∑' x, ((if b x then Pr[= x | p] else 0) +
                  (if b x then Pr[= x | q] else 0))) := by
                  refine tsum_congr fun x => ?_
                  by_cases hx : b x <;> simp [hx]
          _ = (∑' x, if b x then Pr[= x | p] else 0) +
              (∑' x, if b x then Pr[= x | q] else 0) := by rw [ENNReal.tsum_add]
    _ = (Pr[ b | p] + Pr[ b | p]) / 2 := by rw [← h_bad]
    _ = Pr[ b | p] := by
        rw [← two_mul, mul_div_assoc]
        simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- **Boolean-flag form** (the shape the hybrid games expose): if two `SPMF` games agree on
every output where a decidable bad-flag `f` is `false`, have equal flag-`true` probability and
equal failure mass, then their TV distance is bounded by the flag-`true` probability. -/
theorem tvDist_le_probOutput_true_of_identicalOffFlag
    (p q : SPMF α) (f : α → Bool)
    (h_eq : ∀ x, f x = false → Pr[= x | p] = Pr[= x | q])
    (h_flag : Pr[= true | f <$> p] = Pr[= true | f <$> q])
    (h_fail : p.toPMF none = q.toPMF none) :
    SPMF.tvDist p q ≤ (Pr[= true | f <$> p]).toReal := by
  have hbridge : ∀ r : SPMF α, Pr[= true | f <$> r] = Pr[ fun x => f x = true | r] := by
    intro r
    rw [← probEvent_eq_eq_probOutput, probEvent_map]; rfl
  rw [hbridge p]
  refine tvDist_le_probEvent_of_identicalOffBad p q (fun x => f x = true) ?_ ?_ h_fail
  · intro x hx
    exact h_eq x (by simpa using hx)
  · rw [← hbridge p, ← hbridge q]; exact h_flag

end SPMF

/-! ## Axiom audit — kernel-clean. -/
#print axioms SPMF.tvDist_le_probEvent_of_identicalOffBad
#print axioms SPMF.tvDist_le_probOutput_true_of_identicalOffFlag
