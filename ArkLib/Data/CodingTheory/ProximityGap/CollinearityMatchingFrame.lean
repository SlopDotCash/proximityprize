/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CollinearityCensusTransfer

/-!
# The matching frame: collinearity in `Γ_n` IS antipodal balance of a 12-exponent family

Campaign #357, the formal frame for the slanted-census *exactness converse*. The supply
side of the census is closed (chord law, shapes I/II, doubling); what remains is that
nothing else exists. This file converts that question into **pure finite combinatorics**:

* `signedExp` — the sign-normalized exponent family: the six negative terms of the
  collinearity determinant shifted by `2^(m−1)` (through `ζ^(2^(m−1)) = −1`), making all
  twelve weights `+1`.
* `sum_signed_eq` — the term-level shift: the signed 12-term sum equals the unsigned sum
  of the shifted family, over any field with `ζ^(2^(m−1)) = −1`.
* `collinear_iff_balanced` — **the frame**: over any characteristic-zero field with a
  primitive `2^m`-th root, an exponent-triple of `Γ_n` is collinear **iff** the shifted
  12-exponent family is *antipodally balanced*: every residue fiber `t < 2^(m−1)` is
  matched exactly by its antipodal fiber `t + 2^(m−1)`.
* `collinear_iff_balanced_modp` — the same equivalence over `F_p` above the transfer
  threshold `(2^(m−1)·12)^(2^(m−1))`.

**Why this matters**: antipodal balance of a 12-element family is a *matching condition*
in `ℕ` — no field, no polynomial, no characteristic. The exactness converse ("every
collinear triple is chord-law / shape-I / shape-II / doubling") becomes: enumerate the
antipodal matchings of twelve explicit exponent forms and solve each finite linear
system. Per scale this is kernel-decidable; uniformly it is the named 12-term matching
classification, now posed in its final combinatorial form.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (rounds 8–11; the supply-classification comments);
  `FoldedSumThreshold.lean` (`foldedSum_eq_zero_iff_balanced`),
  `CollinearityCensusTransfer.lean` (the 12-term expansion + the transfer engine).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.WindowTwoLayer
open ArkLib.ProximityGap.CollinearityCensusTransfer
open ArkLib.ProximityGap.PairSumRigidityModP

namespace ArkLib.ProximityGap.CollinearityMatchingFrame

/-- The sign-normalized exponent family of the collinearity determinant: negative-weight
terms are shifted by `2^(m−1)` (the antipodal half-turn), so all twelve weights are
`+1`. -/
def signedExp (m : ℕ) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) (x : Fin 12) : ℕ :=
  censusExp a₁ b₁ a₂ b₂ a₃ b₃ x + (if censusWt x = 1 then 0 else 2 ^ (m - 1))

/-- **The term-level shift**: with `ζ^(2^(m−1)) = −1`, the signed 12-term determinant
sum equals the unsigned sum over the shifted family. -/
theorem sum_signed_eq {L : Type*} [Field L] {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ∑ x : Fin 12, ((censusWt x : ℤ) : L) * ζ ^ (censusExp a₁ b₁ a₂ b₂ a₃ b₃ x)
      = ∑ x : Fin 12, ((1 : ℤ) : L) * ζ ^ (signedExp m a₁ b₁ a₂ b₂ a₃ b₃ x) := by
  have hhalf : ζ ^ 2 ^ (m - 1) = -1 := pow_half_eq_neg_one_field hm hζ
  have hwt : ∀ x : Fin 12, censusWt x = 1 ∨ censusWt x = -1 := by decide
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold signedExp
  rcases hwt x with h | h
  · simp [h]
  · simp only [h, if_neg (by norm_num : (-1 : ℤ) ≠ 1)]
    rw [pow_add, hhalf]
    push_cast
    ring

/-- Antipodal balance of an exponent family: every residue fiber `t < 2^(m−1)` is matched
exactly by its antipodal fiber `t + 2^(m−1)`. -/
def Balanced (m : ℕ) (E : Fin 12 → ℕ) : Prop :=
  ∀ t < 2 ^ (m - 1),
    ((univ : Finset (Fin 12)).filter (fun x => E x % 2 ^ m = t)).card
      = ((univ : Finset (Fin 12)).filter
          (fun x => E x % 2 ^ m = t + 2 ^ (m - 1))).card

instance (m : ℕ) (E : Fin 12 → ℕ) : Decidable (Balanced m E) := by
  unfold Balanced
  infer_instance

/-- **THE MATCHING FRAME (characteristic zero).** Over any characteristic-zero field with
a primitive `2^m`-th root, the pencil collinearity equation of an exponent-triple of
`Γ_n` holds **iff** the shifted 12-exponent family is antipodally balanced — collinearity
is a pure matching condition in `ℕ`. -/
theorem collinear_iff_balanced {L : Type*} [Field L] [CharZero L] {m : ℕ}
    (hm : 1 ≤ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ((ζ ^ a₂ + ζ ^ b₂ - (ζ ^ a₁ + ζ ^ b₁)) * (ζ ^ (a₃ + b₃) - ζ ^ (a₁ + b₁))
        = (ζ ^ (a₂ + b₂) - ζ ^ (a₁ + b₁)) * (ζ ^ a₃ + ζ ^ b₃ - (ζ ^ a₁ + ζ ^ b₁)))
      ↔ Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃) := by
  rw [← sub_eq_zero, ← detGamma_expand ζ a₁ b₁ a₂ b₂ a₃ b₃,
    sum_signed_eq hm hζ a₁ b₁ a₂ b₂ a₃ b₃]
  have h1 : (∑ x : Fin 12, ((1 : ℤ) : L) * ζ ^ (signedExp m a₁ b₁ a₂ b₂ a₃ b₃ x) = 0)
      ↔ foldedSum m univ (signedExp m a₁ b₁ a₂ b₂ a₃ b₃) (fun _ => 1) = 0 :=
    (foldedSum_eq_zero_iff_eval_zero hm hζ univ
      (signedExp m a₁ b₁ a₂ b₂ a₃ b₃) (fun _ => 1)).symm
  exact h1.trans (foldedSum_eq_zero_iff_balanced m univ
    (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))

/-- **THE MATCHING FRAME (mod p).** Over `F_p` with `p` above the transfer threshold,
the same equivalence: collinearity in `Γ_n ⊆ F_p²` is the antipodal-balance matching
condition. -/
theorem collinear_iff_balanced_modp {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ)
    (hp : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < p) :
    ((g ^ a₂ + g ^ b₂ - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        = (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) * (g ^ a₃ + g ^ b₃ - (g ^ a₁ + g ^ b₁)))
      ↔ Balanced m (signedExp m a₁ b₁ a₂ b₂ a₃ b₃) := by
  rw [← sub_eq_zero, ← detGamma_expand g a₁ b₁ a₂ b₂ a₃ b₃,
    sum_signed_eq hm hg a₁ b₁ a₂ b₂ a₃ b₃]
  have hbound : (2 ^ (m - 1)
      * l1Weight (univ : Finset (Fin 12)) (fun _ : Fin 12 => (1 : ℤ))) ^ 2 ^ (m - 1)
      < p := by
    have hl1 : l1Weight (univ : Finset (Fin 12)) (fun _ : Fin 12 => (1 : ℤ)) = 12 := by
      decide
    rw [hl1]
    exact hp
  exact (foldedSum_vanishing_iff_char0 hm hg univ (signedExp m a₁ b₁ a₂ b₂ a₃ b₃)
      (fun _ => 1) hbound).trans
    (foldedSum_eq_zero_iff_balanced m univ (signedExp m a₁ b₁ a₂ b₂ a₃ b₃))

/-! ## Source audit -/

#print axioms sum_signed_eq
#print axioms collinear_iff_balanced
#print axioms collinear_iff_balanced_modp

end ArkLib.ProximityGap.CollinearityMatchingFrame
