/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Frontier.SmoothDeepMcaThreshold

/-! # Exact list boundaries from consecutive agreement counts on a smooth coset

At `t = k + 1 + a` agreements, a prescribed-product fiber with `a` prescribed
coefficients witnesses failure. At `t + 1` agreements, disjoint interpolation
samples certify safety. Both tests use just the integer parameters.
-/

namespace ProximityGap.SmoothListPackingRadius
open Code ListInterpolationBoundary
open scoped ENNReal

/-- Sufficient integer tests for an exact first failing error count `n - (k + 1 + a)`
on every smooth domain and at every positive width. -/
theorem good_iff {I F : Type} [Fintype I] [Nonempty I] [Fintype F] [Field F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] {k m a B : ℕ} (hk : 0 < k) (hm : 0 < m)
    (ht : k + 1 + a ≤ Fintype.card I)
    (hlower : Fintype.card I * Fintype.card F ^ a * B < (Fintype.card I).choose (k + 1 + a))
    (hupper : (Fintype.card I).choose k / (k + 1 + a + 1).choose k ≤ B) (δ : ℝ) :
    Lambda (words D k m) δ ≤ (B : ℕ∞) ↔
      δ < ((Fintype.card I - (k + 1 + a) : ℕ) : ℝ) / Fintype.card I := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  constructor
  · contrapose!
    intro hδ
    have lower := SmoothDeepMcaThreshold.smooth_list_lower D hk hlower
    have diag := Lambda_le_of_injective_comp (C := (ReedSolomon.code D k : Set (I → F)))
      (D := words D k m) (e := fun (x : F) (_ : Fin m) => x)
      (fun _ _ h => congrFun h ⟨0, hm⟩) (fun _ h _ => h)
      (((Fintype.card I - (k + 1 + a) : ℕ) : ℝ) / Fintype.card I)
    exact lower.trans_le (diag.trans (Lambda_mono hδ))
  · intro hδ
    rw [lt_div_iff₀ hn, Nat.cast_sub ht] at hδ
    have upper := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D k (k + 1 + a + 1)
      m δ (by omega) (by push_cast at hδ ⊢; linarith)
    exact upper.trans (by exact_mod_cast hupper)

/-- With positive budget and `q ≥ 4 n²`, prescribing at least one additional
coefficient can never pass both adjacent tests. This bounds the search for a
product certificate independently of the code dimension. -/
theorem no_deeper_window {n k a B q : ℕ} (ha : 0 < a) (hB : 0 < B)
    (ht : k + 1 + a ≤ n) (hq : 4 * n ^ 2 ≤ q)
    (hlower : n * q ^ a * B < n.choose (k + 1 + a)) :
    B < n.choose k / (k + 1 + a + 1).choose k := by
  let t := k + 1 + a
  have ht' : t ≤ n := ht
  have hkt : k ≤ t := by dsimp [t]; omega
  have hn : 0 < n := by omega
  have positive : 0 < (t + 1).choose k := Nat.choose_pos (by omega)
  have hqpos : 0 < q := by nlinarith
  have mult := Nat.add_one_mul_choose_eq t (t - k)
  rw [Nat.choose_symm hkt, show t - k + 1 = t + 1 - k by omega, Nat.choose_symm (by omega)] at mult
  have step : (t + 1).choose k ≤ (t + 1) * t.choose k := by
    rw [mult]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have powers : 4 * n ^ (a + 1) ≤ q ^ a := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [pow_succ q]
    calc 4 * n ^ (b + 1 + 1) = (4 * n ^ 2) * n ^ b := by ring
      _ ≤ q * q ^ b := Nat.mul_le_mul hq (Nat.pow_le_pow_left (by nlinarith) b)
      _ = _ := mul_comm _ _
  have skip : (n - k).choose (t - k) ≤ n ^ (a + 1) := by
    rw [show t - k = a + 1 by dsimp [t]; omega]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  have count : 2 * n.choose t * (t + 1).choose k ≤ n * q ^ a * n.choose k := calc
    _ ≤ 2 * n.choose t * ((t + 1) * t.choose k) := Nat.mul_le_mul_left _ step
    _ = 2 * (t + 1) * (n.choose t * t.choose k) := by ring
    _ = 2 * (t + 1) * (n.choose k * (n - k).choose (t - k)) := by rw [Nat.choose_mul hkt]
    _ ≤ 2 * (t + 1) * (n.choose k * n ^ (a + 1)) := by gcongr
    _ ≤ 2 * (2 * n) * (n.choose k * n ^ (a + 1)) := by gcongr; omega
    _ = n * (4 * n ^ (a + 1)) * n.choose k := by ring
    _ ≤ _ := by gcongr
  change B < n.choose k / (t + 1).choose k
  by_contra! upper
  have small := (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_of_le upper)
  have small' := small.trans_le (Nat.mul_le_mul_right ((t + 1).choose k)
    (show B + 1 ≤ 2 * B by omega))
  have left := Nat.mul_lt_mul_of_pos_left small' (Nat.mul_pos hn (pow_pos hqpos a))
  have right := Nat.mul_lt_mul_of_pos_right hlower (Nat.mul_pos (by decide : 0 < 2) positive)
  change n * q ^ a * B * (2 * (t + 1).choose k) < n.choose t * (2 * (t + 1).choose k) at right
  nlinarith only [left, right, count]

#print axioms no_deeper_window
#print axioms good_iff
end ProximityGap.SmoothListPackingRadius
