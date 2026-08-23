/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SupportSqBound
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# CS25 #82: first moment + Paley-Zygmund covered-set reduction

For a finite code `𝒞 ⊆ (ι → F)` and Hamming radius `r`, let `closeCount w = #{c ∈ 𝒞 : Δ₀(w,c) ≤ r}`.
Two facts reduce the *covered fraction* to a second-moment input:

* **First moment** `∑_w closeCount w = |𝒞| · V`, where `V = #{w : Δ₀(w,0) ≤ r}` is the (center-free)
  Hamming-ball volume.
* **Paley-Zygmund covered-set bound** `(|𝒞|·V)² ≤ |close| · ∑_w (closeCount w)²`, where
  `close = {w : Δ₀(w,𝒞) ≤ r}` is the covered set.  Hence `|close| ≥ (|𝒞|·V)² / E[N²]`.

This is the full covered-set machinery for CS25 T4.17 (#82): the only remaining input is the
second-moment bound `E[N²] = ∑_w (closeCount w)²`, i.e. the RS/MDS pair-distance (weight enumerator)
analysis.  Everything else — first moment, Cauchy-Schwarz engine, and the covering existence
(`CS25CoveringExistence.lean`) — is now proven.
-/

open scoped BigOperators

namespace ArkLib.CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- Hamming distance is translation invariant: `Δ₀(w, c) = Δ₀(w - c, 0)`. -/
theorem hammingDist_sub_right (w c : ι → F) :
    hammingDist w c = hammingDist (w - c) (0 : ι → F) := by
  unfold hammingDist
  congr 1
  ext i
  simp [Pi.sub_apply, sub_ne_zero]

/-- The Hamming ball volume is independent of its center. -/
theorem ball_card_center_indep (c : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F => hammingDist w c ≤ r)).card
      = (Finset.univ.filter (fun w : ι → F => hammingDist w (0 : ι → F) ≤ r)).card := by
  classical
  refine Finset.card_bij' (fun w _ => w - c) (fun v _ => v + c) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, by rw [← hammingDist_sub_right]; exact hw.2⟩
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hammingDist_sub_right]; simpa using hv.2
  · intro w _; simp
  · intro v _; simp

/-- The per-word count of close codewords. -/
noncomputable def closeCount (𝒞 : Finset (ι → F)) (r : ℕ) (w : ι → F) : ℕ :=
  (𝒞.filter (fun c => hammingDist w c ≤ r)).card

/-- **First moment.** `∑_w #{c ∈ 𝒞 : Δ₀(w,c) ≤ r} = |𝒞| · V`. -/
theorem sum_closeCount_eq (𝒞 : Finset (ι → F)) (r : ℕ) :
    (∑ w : ι → F, closeCount 𝒞 r w)
      = 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w (0 : ι → F) ≤ r)).card := by
  classical
  have hcc : ∀ w : ι → F,
      closeCount 𝒞 r w = ∑ c ∈ 𝒞, (if hammingDist w c ≤ r then 1 else 0) := by
    intro w; rw [closeCount, Finset.card_filter]
  simp_rw [hcc]
  rw [Finset.sum_comm]
  have h : ∀ c ∈ 𝒞,
      (∑ w : ι → F, if hammingDist w c ≤ r then 1 else 0)
        = (Finset.univ.filter (fun w : ι → F => hammingDist w (0 : ι → F) ≤ r)).card := by
    intro c _
    rw [← Finset.card_filter]
    exact ball_card_center_indep c r
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]

/-- **Paley-Zygmund covered-set bound.** `(|𝒞|·V)² ≤ |close| · ∑_w (closeCount w)²`, where
`close = {w : closeCount w ≠ 0} = {w : Δ₀(w,𝒞) ≤ r}` is the covered set.  Hence the covered set has
size at least `(|𝒞|·V)² / E[N²]`; only the second moment `∑_w (closeCount w)²` remains as input. -/
theorem sq_card_mul_volume_le_card_close_mul_sum_sq (𝒞 : Finset (ι → F)) (r : ℕ) :
    (𝒞.card *
        (Finset.univ.filter (fun w : ι → F => hammingDist w (0 : ι → F) ≤ r)).card) ^ 2
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
          * (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2) := by
  rw [← sum_closeCount_eq 𝒞 r]
  exact ArkLib.sq_sum_le_card_support_mul_sum_sq (closeCount 𝒞 r)

end ArkLib.CS25
