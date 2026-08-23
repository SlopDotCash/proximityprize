/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilCorankTwo

/-!
# Threshold consumers for the WB-5 corank-two count (#371)

`WBPencilCorankTwo.lean` proves the fixed-stack corank-two bad-scalar count.  This file
packages the long double-anchor/twin-freeness hypotheses as a reusable certificate and
lifts a uniform certificate theorem to the prize-side `epsMCA` and `mcaDeltaStar` APIs.
-/

open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.WBPencil

open Polynomial
open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- The polynomial budget proved by the WB-5 corank-two count. -/
def corank2Budget (n w : ℕ) : ℕ :=
  (w + 1) + (n + 1) + n * n * (2 * w + 2)

/-- A stack has a WB-5 corank-two certificate when both words admit the prescribed
window representations, the double-update anchor is nonzero, and all pair-coincidence
polynomials are twin-free. -/
def HasCorankTwoCertificate (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F) :
    Prop :=
  ∃ (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (c₀ c₀' cs cs' : WCol n k w),
    ℓ₀.natDegree ≤ w ∧
    ℓ₁.natDegree ≤ w ∧
    R₀.natDegree ≤ w + k - 1 ∧
    R₁.natDegree ≤ w + k - 1 ∧
    (∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i)) ∧
    (∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i)) ∧
    c₀ ≠ c₀' ∧
    (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det ≠ 0 ∧
    ∀ i j : Fin n, i ≠ j →
      coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0

open Classical in
/-- The WB-5 count in certificate form. -/
theorem badScalars_card_le_of_hasCorankTwoCertificate (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} (hcert : HasCorankTwoCertificate dom k w u₀ u₁) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ corank2Budget n w := by
  letI := Classical.decEq F
  rcases hcert with
    ⟨ℓ₀, R₀, ℓ₁, R₁, J, c₀, c₀', cs, cs', hd₀, hd₁, hr₀, hr₁,
      hrel₀, hrel₁, hcc, hdet, htwin⟩
  simpa [corank2Budget] using
    badScalars_card_le_of_corank2 dom hk hδn hd₀ hd₁ hr₀ hr₁ hrel₀ hrel₁
      hcc hdet htwin

open Classical in
/-- A uniform WB-5 certificate theorem gives the corresponding `epsMCA` bound. -/
theorem epsMCA_le_of_forall_hasCorankTwoCertificate (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hcert : ∀ u₀ u₁ : Fin n → F, HasCorankTwoCertificate dom k w u₀ u₁) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (corank2Budget n w : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  letI := Classical.decEq F
  epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ
    (corank2Budget n w)
    (fun u => badScalars_card_le_of_hasCorankTwoCertificate dom hk hδn
      (hcert (u 0) (u 1)))

open Classical in
/-- Threshold form of the uniform WB-5 certificate consumer. -/
theorem le_mcaDeltaStar_of_forall_hasCorankTwoCertificate (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hcert : ∀ u₀ u₁ : Fin n → F, HasCorankTwoCertificate dom k w u₀ u₁)
    {εstar : ℝ≥0∞}
    (hbudget : (corank2Budget n w : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  letI := Classical.decEq F
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_of_forall_hasCorankTwoCertificate dom hk hδn hcert) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_hasCorankTwoCertificate
#print axioms ProximityGap.WBPencil.epsMCA_le_of_forall_hasCorankTwoCertificate
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_of_forall_hasCorankTwoCertificate
