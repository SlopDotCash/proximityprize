/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowChainStructure

/-!
# The shared-factor kill (#371, strata map)

**A nontrivial common locator factor admits no defect witnesses**: if
`h ∣ ℓ₀`, `h ∣ ℓ₁`, and `h` is domain-nonvanishing of positive degree, then no
identity `R₀ℓ₁ + γ·R₁ℓ₀ − p·ℓ₀ℓ₁ = g·m_S` with constant-bounded `g ≠ 0` and a
large witness can hold: reducing mod `h` kills the left side termwise
(`h ∣ R₀ℓ₁` needs care — it holds when `h ∣ ℓ₁`), and coprimality with `m_S`
pushes `h` into `g`, whose degree is too small.

This closes the `gcd(ℓ₀, ℓ₁) ≠ 1` stratum of the window analysis: such stacks
have NO bad scalars beyond the zero-class, at every window row with
`deg g < deg h` — in particular the first row (`g` constant, any `deg h ≥ 1`).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The shared-factor kill.**  A common domain-nonvanishing locator factor of
positive degree contradicts any defect identity whose multiplier has smaller
degree. -/
theorem shared_factor_no_defect (dom : Fin n ↪ F)
    {ℓ₀ R₀ ℓ₁ R₁ h : F[X]} (hdvd₀ : h ∣ ℓ₀) (hdvd₁ : h ∣ ℓ₁)
    (hGh : ∀ i, h.eval (dom i) ≠ 0)
    {γ p : F} {g : F[X]} (hg : g ≠ 0) {S : Finset (Fin n)}
    (hgdeg : g.natDegree < h.natDegree)
    (hid : R₀ * ℓ₁ + C γ * (R₁ * ℓ₀) - C p * (ℓ₀ * ℓ₁)
      = g * vanishingPoly dom S) :
    False := by
  obtain ⟨q₀, rfl⟩ := hdvd₀
  obtain ⟨q₁, rfl⟩ := hdvd₁
  -- h divides the left side termwise
  have hdvdL : h ∣ g * vanishingPoly dom S := by
    refine ⟨R₀ * q₁ + C γ * (R₁ * q₀) - C p * (h * q₀ * q₁), ?_⟩
    linear_combination -hid
  have hcopS : IsCoprime h (vanishingPoly dom S) :=
    isCoprime_vanishingPoly dom hGh S
  have hdvdg : h ∣ g := hcopS.dvd_of_dvd_mul_right hdvdL
  have hdeg := Polynomial.natDegree_le_of_dvd hdvdg hg
  omega

section CodewordRow

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The codeword-row kill** (any linear code, any k): if the first row IS a
codeword, no nonzero scalar is bad — the line's explanation transports to a
joint explanation `(u₀, γ⁻¹·(w − u₀))`. -/
theorem codeword_fst_not_bad (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hu₀ : u₀ ∈ C) {γ : F} (hγ : γ ≠ 0) :
    ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  rintro ⟨S, hsz, ⟨wc, hwc, hag⟩, hno⟩
  refine hno ⟨u₀, hu₀, γ⁻¹ • (wc - u₀),
    C.smul_mem _ (C.sub_mem hwc hu₀), fun i hi => ⟨rfl, ?_⟩⟩
  have h := hag i hi
  rw [Pi.smul_apply, Pi.sub_apply, h, add_sub_cancel_left,
    smul_smul, inv_mul_cancel₀ hγ, one_smul]

open Classical in
/-- The bad-scalar count of a codeword-first-row stack is at most one. -/
theorem codeword_fst_badScalars_card_le_one (C : Submodule F (ι → A)) (δ : ℝ≥0)
    {u₀ u₁ : ι → A} (hu₀ : u₀ ∈ C) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      (C : Set (ι → A)) δ u₀ u₁ γ)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_singleton 0))
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  rw [Finset.mem_singleton]
  by_contra hne
  exact codeword_fst_not_bad C δ hu₀ hne hγ.2

end CodewordRow

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.shared_factor_no_defect
#print axioms ProximityGap.WBPencil.codeword_fst_not_bad
#print axioms ProximityGap.WBPencil.codeword_fst_badScalars_card_le_one
