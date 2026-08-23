/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightGradedAssembly

/-!
# The graded weight collapse with the coefficient budget abstracted

`betaRec_weight_le_graded` (`BetaWeightGradedAssembly.lean`) proves the graded App-A.4 weight
collapse for the recursion capsule at the **unsigned** canonical family `B_coeff`, with the
per-coefficient budget discharged inline by `B_coeff_weight_le_graded`.  The signed-family
variant needed by the genuine-monic capstone (`GenuineMonicCapstone.lean`:
`betaRec_weight_le_graded_signed`, at `BcoeffSigned = −B_coeff`) re-proves the same collapse
with the budget transported through `weight_Λ_over_𝒪_neg`.

This file isolates the reusable core: **the collapse with the budget as a hypothesis**.  Every
other ingredient of the proof — the monic `W`-weight, `weight_ξ_bound`, the base case
`weight_mk_X_le`, and the `htele` telescoping arithmetic (`GradedHtele.graded_htele_arith`) — is
independent of the coefficient family and retained verbatim.  Any future coefficient family
(cleared, normalized, or otherwise re-signed variants of the canonical Faà-di-Bruno
coefficients) obtains the graded collapse — and through it the `hcardFin` front of the
off-centre §5 bundle — from its budget alone, with no re-derivation of the telescoping.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Appendix A.2 (weight `Λ`), A.4 (recursion `(A.1)`, Claim A.2).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-- **The graded weight theorem, budget-abstracted.**  Identical to `betaRec_weight_le_graded`
except that the per-coefficient budget (there discharged by `B_coeff_weight_le_graded` for the
unsigned canonical family) is taken as the hypothesis `hbB`; in exchange the paper grading `hR`
is not needed.  All other bullets are coefficient-independent and reproduced verbatim.

Instantiations: `Bcoeff := B_coeff` with `hbB := B_coeff_weight_le_graded` recovers
`betaRec_weight_le_graded`; `Bcoeff := BcoeffSigned` with the budget transported through
`weight_Λ_over_𝒪_neg` recovers `GenuineMonicCapstone.betaRec_weight_le_graded_signed`. -/
theorem betaRec_weight_le_graded_of_budget (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 hH (Bcoeff i₁ p) D
          ≤ (WithBot.some ((Bivariate.natDegreeY R - Multiset.card p.parts)
              * (D - H.natDegree + 1) + (D - Multiset.card p.parts)) : WithBot ℕ)) :
    ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some
          ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D + (D - H.natDegree + 1))
              * (2 * t - 1)
            + (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  set d := Bivariate.natDegreeY R with hd
  set A := D - H.natDegree + 1 with hA
  set α := d * A + D + A with hα
  refine betaRec_weight_le_excl x₀ R H hHyp Bcoeff
    hD hH (bW := 0) (bξ := (d - 1) * A)
    (bB := fun i₁ {m} p => (d - Multiset.card p.parts) * A + (D - Multiset.card p.parts))
    (wβ := fun t => α * (2 * t - 1) + A) ?_ ?_ ?_ ?_ ?_
  · -- hbW (monic)
    simpa using
      BCIKS20.HenselNumerator.W𝒪_weight_le_zero_of_monic H hmonic hH hD
  · -- hbξ via weight_ξ_bound
    have h := weight_ξ_bound (H := H) (R := R) x₀ hH hHyp hd2 hD hD_Rx0
    have hbridge : (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)
        = (d - 1) * A := by
      have : Bivariate.natDegreeY H = H.natDegree := rfl
      rw [this, ← hd, ← hA]
    rwa [hbridge] at h
  · -- hbB: the abstract budget hypothesis
    intro i₁ m p
    exact hbB i₁ p
  · -- hβ0: weight(mk X) ≤ wβ 0 = α·0 + A = A
    have h := weight_mk_X_le (H := H) hD hH hdHD
    simpa [← hA] using h
  · -- htele (non-forbidden)
    intro s i₁ hi₁ p hexcl
    have hi₁' : i₁ < s + 2 := Finset.mem_range.mp hi₁
    beta_reduce
    rw [partsCount_affine_sum p α A, mul_zero, zero_add,
      show betaξExp i₁ p = 2 * i₁ + Multiset.card p.parts - 2 from rfl]
    set σ := Multiset.card p.parts with hσ
    rcases Nat.eq_zero_or_pos σ with hσ0 | hσ1
    · -- empty partition: m = 0, i₁ = s+1
      have hcard0 : Multiset.card p.parts = 0 := by rw [← hσ]; exact hσ0
      have hp0 : p.parts = 0 := Multiset.card_eq_zero.mp hcard0
      have hm0 : s + 1 - i₁ = 0 := by
        have hps := p.parts_sum
        rw [hp0] at hps
        simp at hps
        omega
      have hi : i₁ = s + 1 := by omega
      rw [hσ0, hm0]
      simp only [Nat.sub_zero, mul_zero, add_zero]
      rw [show 2 * i₁ - 2 = 2 * s from by omega]
      have hstep : 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right A (Nat.sub_le d 1))
      have h1 : 2 * s * ((d - 1) * A) + (d * A + D) ≤ α * (2 * s) + α := by
        have hα_ge : d * A ≤ α := by rw [hα]; omega
        have h2 : 2 * s * ((d - 1) * A) ≤ α * (2 * s) := by
          calc 2 * s * ((d - 1) * A) ≤ 2 * s * (d * A) := hstep
            _ ≤ 2 * s * α := Nat.mul_le_mul_left _ hα_ge
            _ = α * (2 * s) := Nat.mul_comm _ _
        have h3 : d * A + D ≤ α := by rw [hα]; omega
        omega
      calc 2 * s * ((d - 1) * A) + (d * A + D)
          ≤ α * (2 * s) + α := h1
        _ = α * (2 * s + 1) := by ring
        _ ≤ α * (2 * (s + 1) - 1) + A := by
            have : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
            rw [this]
            omega
    · -- σ ≥ 1: bridge forbidden to (i₁=0 ∧ σ=1), then graded_htele_arith
      have hexcl' : ¬(i₁ = 0 ∧ σ = 1) := by
        rintro ⟨hi0, hσ1'⟩
        apply hexcl
        refine ⟨hi0, ?_⟩
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (hσ ▸ hσ1')
        have hsum := p.parts_sum
        rw [ha] at hsum ⊢
        simp at hsum
        rw [hsum]
        subst hi0
        norm_num
      have harith := GradedHtele.graded_htele_arith d D H.natDegree
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)) (by omega) hdHD
        i₁ σ hσ1 hexcl'
      have hσm : σ ≤ s + 1 - i₁ := by
        rw [hσ]
        exact betaRec_card_le p
      have hkey : 2 * i₁ + σ - 1 + (2 * (s + 1 - i₁) - σ) = 2 * s + 1 := by omega
      have hAσ : (D - H.natDegree + 1) * σ = A * σ := by rw [hA]
      have := Nat.add_le_add_right harith (α * (2 * (s + 1 - i₁) - σ))
      calc (2 * i₁ + σ - 2) * ((d - 1) * A)
            + ((d - σ) * A + (D - σ))
            + (α * (2 * (s + 1 - i₁) - σ) + A * σ)
          = ((2 * i₁ + σ - 2) * ((d - 1) * (D - H.natDegree + 1))
              + ((d - σ) * (D - H.natDegree + 1) + (D - σ))
              + (D - H.natDegree + 1) * σ) + α * (2 * (s + 1 - i₁) - σ) := by
            rw [← hA]; ring
        _ ≤ ((d * (D - H.natDegree + 1) + D + (D - H.natDegree + 1)) * (2 * i₁ + σ - 1)
              + (D - H.natDegree + 1)) + α * (2 * (s + 1 - i₁) - σ) := Nat.add_le_add_right harith _
        _ = α * (2 * i₁ + σ - 1) + α * (2 * (s + 1 - i₁) - σ) + A := by rw [hα, hA]; ring
        _ = α * ((2 * i₁ + σ - 1) + (2 * (s + 1 - i₁) - σ)) + A := by ring
        _ = α * (2 * s + 1) + A := by rw [hkey]
        _ = α * (2 * (s + 1) - 1) + A := by rw [show (2 * (s + 1) - 1 : ℕ) = 2 * s + 1 from by omega]

end ArkLib

/-! ## Axiom audit — must rest only on `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.betaRec_weight_le_graded_of_budget
