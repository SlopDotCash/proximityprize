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
lifts it to the prize-side `epsMCA` and `mcaDeltaStar` APIs.

**A certificate cannot be required for every stack.**  The certificate demands a nonzero
double-update anchor determinant, and degenerate stacks have none: at the first beyond-UDR
slice `n = 4`, `k = 1`, `w = 2`, the zero stack forces both numerators `R₀ = R₁ = 0`, so all
three locator columns of `windowPencil` vanish, and replacing only two rows by coordinate
singletons leaves a zero column.  `no_zero_stack_certificate` and
`not_forall_hasCorankTwoCertificate` check this, so a hypothesis
`∀ u₀ u₁, HasCorankTwoCertificate dom 1 2 u₀ u₁` is unsatisfiable (a vacuous premise, not a
Lean inconsistency).  The threshold consumers below therefore take a *split* hypothesis:
each stack either carries a certificate or already meets the budget directly (as the zero
stack does, `zeroStack_badScalars_card_eq_zero`).  Producing that split for the nontrivial
stacks is the remaining obligation; this file does not prove it.
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

/-! ## The uniform certificate premise is unsatisfiable on the zero stack

At `n = 4`, `k = 1`, `w = 2` (the first beyond-UDR slice) no zero stack has a certificate,
so no theorem may assume a certificate for every stack. -/

/-- Two coordinate-singleton row updates cannot reach all three locator columns. -/
theorem exists_locator_col_ne (cs cs' : WCol 4 1 2) :
    ∃ t : Fin 3, (Sum.inl t : WCol 4 1 2) ≠ cs ∧ Sum.inl t ≠ cs' := by
  fin_cases cs <;> fin_cases cs' <;> decide

omit [Fintype F] in
/-- With both numerators zero, every double-update anchor matrix has a zero locator column,
so its determinant vanishes. -/
theorem pencilSqDU_det_eq_zero_of_numerators_zero (dom : Fin 4 ↪ F)
    (ℓ₀ ℓ₁ : F[X]) (J : WCol 4 1 2 → Fin 7) (c₀ c₀' cs cs' : WCol 4 1 2) :
    (pencilSqDU dom 1 2 ℓ₀ 0 ℓ₁ 0 J c₀ c₀' cs cs').det = 0 := by
  classical
  obtain ⟨t, ht, ht'⟩ := exists_locator_col_ne cs cs'
  apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inl t)
  intro i
  simp [pencilSqDU, Matrix.updateRow_apply, ht, ht', windowPencil, Matrix.submatrix_apply]

omit [Fintype F] in
/-- A numerator of degree `≤ 2` representing the zero word on four distinct points is zero. -/
theorem numerator_eq_zero_of_zero_word (dom : Fin 4 ↪ F) (ℓ R : F[X])
    (hdeg : R.natDegree ≤ 2) (hrel : ∀ i, ℓ.eval (dom i) * (0 : F) = R.eval (dom i)) :
    R = 0 := by
  classical
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
    (s := Finset.univ.image dom)
  · rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast (by omega : R.natDegree < 4))
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simpa using (hrel i).symm

omit [Fintype F] in
/-- **The zero stack has no corank-two certificate** at `n = 4`, `k = 1`, `w = 2`. -/
theorem no_zero_stack_certificate (dom : Fin 4 ↪ F) :
    ¬ HasCorankTwoCertificate dom 1 2 (0 : Fin 4 → F) 0 := by
  classical
  rintro ⟨ℓ₀, R₀, ℓ₁, R₁, J, c₀, c₀', cs, cs', _, _, hr₀, hr₁, hrel₀, hrel₁, _, hdet, _⟩
  have hR₀ : R₀ = 0 := numerator_eq_zero_of_zero_word dom ℓ₀ R₀ (by simpa using hr₀) hrel₀
  have hR₁ : R₁ = 0 := numerator_eq_zero_of_zero_word dom ℓ₁ R₁ (by simpa using hr₁) hrel₁
  subst hR₀ hR₁
  exact hdet (pencilSqDU_det_eq_zero_of_numerators_zero dom ℓ₀ ℓ₁ J c₀ c₀' cs cs')

omit [Fintype F] in
/-- **The uniform certificate premise is unsatisfiable**: no domain of size `4` admits a
corank-two certificate for every stack at `k = 1`, `w = 2`. -/
theorem not_forall_hasCorankTwoCertificate (dom : Fin 4 ↪ F) :
    ¬ (∀ u₀ u₁ : Fin 4 → F, HasCorankTwoCertificate dom 1 2 u₀ u₁) :=
  fun h => no_zero_stack_certificate dom (h 0 0)

open Classical in
omit [NeZero n] in
/-- The zero stack has no bad scalar for a linear code: the zero codeword pair agrees with
it jointly on every set.  So the degenerate stack meets any budget without a certificate. -/
theorem zeroStack_badScalars_card_eq_zero (dom : Fin n ↪ F) (k : ℕ) (δ : ℝ≥0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (0 : Fin n → F) 0 γ)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro γ - ⟨S, -, -, hnj⟩
  exact hnj ⟨0, (rsCode dom k).zero_mem, 0, (rsCode dom k).zero_mem,
    fun i _ => ⟨rfl, rfl⟩⟩

/-! ## Threshold consumers with a split hypothesis

Each stack either carries a certificate or meets the budget directly.  The certificate is
only needed on the nontrivial branch; degenerate stacks such as the zero stack take the
direct branch. -/

open Classical in
/-- Certificates on the nontrivial stacks, plus a direct count on the remaining ones, give the
`epsMCA` bound. -/
theorem epsMCA_le_of_forall_certificate_or_badCount_le (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hsplit : ∀ u₀ u₁ : Fin n → F, HasCorankTwoCertificate dom k w u₀ u₁ ∨
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ corank2Budget n w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (corank2Budget n w : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  letI := Classical.decEq F
  epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ
    (corank2Budget n w)
    (fun u => (hsplit (u 0) (u 1)).elim
      (fun hcert => badScalars_card_le_of_hasCorankTwoCertificate dom hk hδn hcert)
      (fun hcount => by convert hcount))

open Classical in
/-- Threshold form of the split WB-5 certificate consumer. -/
theorem le_mcaDeltaStar_of_forall_certificate_or_badCount_le (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hsplit : ∀ u₀ u₁ : Fin n → F, HasCorankTwoCertificate dom k w u₀ u₁ ∨
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ corank2Budget n w)
    {εstar : ℝ≥0∞}
    (hbudget : (corank2Budget n w : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  letI := Classical.decEq F
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_of_forall_certificate_or_badCount_le dom hk hδn hsplit) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_hasCorankTwoCertificate
#print axioms ProximityGap.WBPencil.no_zero_stack_certificate
#print axioms ProximityGap.WBPencil.not_forall_hasCorankTwoCertificate
#print axioms ProximityGap.WBPencil.zeroStack_badScalars_card_eq_zero
#print axioms ProximityGap.WBPencil.epsMCA_le_of_forall_certificate_or_badCount_le
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_of_forall_certificate_or_badCount_le
