/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Mutual correlated agreement with loss

`IsMCA` asks that every large agreement set `T` of a generated word extend to the generating
words on that same `T`. Lossy MCA (`IsLossyMCA`) allows the extension to drop up to `loss · n`
points of `T`: outside the error event, for every agreement set `T` of the generated word with
`|T| ≥ (1 - δ) n`, all generating words agree with codewords on a common subset `T' ⊆ T` with
`|T \ T'| ≤ loss · n`. At `loss = 0` this is `IsMCA` (`isLossyMCA_zero_iff`).

The loss is what lets the error be independent of the block length `n` in the unique-decoding
regime: correlated agreement there holds with `O(1)` exceptional seeds up to a proximity loss
([BCHKS25, Theorem 1.3]), while lossless MCA needs `Ω(n)`.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S., *On Proximity Gaps for
  Reed–Solomon Codes*][BCHKS25]
-/


namespace CoreDefinitions

open NNReal ENNReal unitInterval LinearCode
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ : Type} [Fintype ℓ]

/-- The lossy MCA bad event at seed `x`: the generated word agrees with the code on a set `T`
of at least `(1 - δ) n` points, but on no subset of `T` missing at most `loss · n` points do all
the generating words agree with the code. -/
def IsLossyMCA {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A)
    (x : S) (U : ℓ → (ι → A)) (δ loss : ℝ) : Prop :=
  let v : ι → A := fun k => ∑ j, G x j • U j k
  ∃ T : Finset ι, (T.card : ℝ) ≥ (Fintype.card ι) * (1 - δ) ∧
    projectedWord v T ∈ projectedCodeSubmod MC T ∧
    ∀ T' ⊆ T, (T'.card : ℝ) ≥ T.card - loss * Fintype.card ι →
      ∃ j : ℓ, projectedWord (U j) T' ∉ projectedCodeSubmod MC T'

/-- The lossy MCA error: the largest probability of the lossy MCA bad event over the generating
words. -/
noncomputable def lossyMcaError {S : Type} [Nonempty S] [Fintype S] [SampleableType S]
    {A : Type} [AddCommMonoid A] [Module F A]
    (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ loss : ℝ) : ENNReal :=
  ⨆ U : ℓ → (ι → A), Pr{let x ←$ᵗ S}[IsLossyMCA G MC x U δ loss]

section Lemmas

variable {S : Type} [Nonempty S] [Fintype S] {A : Type} [AddCommMonoid A] [Module F A]

/-- Without loss, the only admissible subset of `T` is `T` itself, so lossy MCA is MCA. -/
theorem isLossyMCA_zero_iff (G : Generator S ℓ F) (MC : ModuleCode ι F A) (x : S)
    (U : ℓ → (ι → A)) (δ : ℝ) :
    IsLossyMCA G MC x U δ 0 ↔ IsMCA G MC x U δ := by
  constructor
  · rintro ⟨T, hT, hv, hbad⟩
    exact ⟨T, hT, hv, hbad T subset_rfl (by simp)⟩
  · rintro ⟨T, hT, hv, j, hj⟩
    refine ⟨T, hT, hv, fun T' hT' hcard ↦ ⟨j, ?_⟩⟩
    rw [Finset.eq_of_subset_of_card_le hT' (by simpa using hcard)]
    exact hj

/-- A larger loss admits more subsets `T'`, each of which must fail, so the lossy MCA bad event
shrinks as the loss grows. -/
theorem IsLossyMCA.of_loss_le {G : Generator S ℓ F} {MC : ModuleCode ι F A} {x : S}
    {U : ℓ → (ι → A)} {δ loss loss' : ℝ} (h : IsLossyMCA G MC x U δ loss')
    (hloss : loss ≤ loss') : IsLossyMCA G MC x U δ loss := by
  obtain ⟨T, hT, hv, hbad⟩ := h
  refine ⟨T, hT, hv, fun T' hT' hcard ↦ hbad T' hT' ?_⟩
  have : loss * Fintype.card ι ≤ loss' * Fintype.card ι :=
    mul_le_mul_of_nonneg_right hloss (Nat.cast_nonneg _)
  linarith

variable [SampleableType S]

/-- At zero loss the lossy MCA error is the MCA error. -/
theorem lossyMcaError_zero (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ) :
    lossyMcaError G MC δ 0 = mcaError G MC δ := by
  unfold lossyMcaError mcaError
  simp only [isLossyMCA_zero_iff]

/-- The lossy MCA error is antitone in the loss. -/
theorem lossyMcaError_anti (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ)
    {loss loss' : ℝ} (hloss : loss ≤ loss') :
    lossyMcaError G MC δ loss' ≤ lossyMcaError G MC δ loss :=
  iSup_mono fun _ ↦ prEvent_mono _ _ _ fun _ h ↦ h.of_loss_le hloss

/-- A nonnegative loss can only lower the MCA error. -/
theorem lossyMcaError_le_mcaError (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ : ℝ)
    {loss : ℝ} (hloss : 0 ≤ loss) : lossyMcaError G MC δ loss ≤ mcaError G MC δ :=
  (lossyMcaError_anti G MC δ hloss).trans (lossyMcaError_zero G MC δ).le

/-- The lossy MCA error is a probability, so it is finite. -/
theorem lossyMcaError_ne_top (G : Generator S ℓ F) (MC : ModuleCode ι F A) (δ loss : ℝ) :
    lossyMcaError G MC δ loss ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ prEvent_le_one _)

end Lemmas

end CoreDefinitions

#print axioms CoreDefinitions.isLossyMCA_zero_iff
#print axioms CoreDefinitions.IsLossyMCA.of_loss_le
#print axioms CoreDefinitions.lossyMcaError_zero
#print axioms CoreDefinitions.lossyMcaError_anti
#print axioms CoreDefinitions.lossyMcaError_le_mcaError
#print axioms CoreDefinitions.lossyMcaError_ne_top
