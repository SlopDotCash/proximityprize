/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCAJohnsonMutualExtract

/-! # Quantified joint agreement from two proximates (toward MCA Johnson)

Combining `affineLine_mutual_extract` with inclusion–exclusion: two Reed–Solomon
proximates of the affine line `f₀+γf₁` (at distinct slopes), with agreement sets
`A, A'`, yield a codeword pair `(p₀,p₁)` jointly matching `(f₀,f₁)` on `A ∩ A'`,
a set of size `≥ |A| + |A'| − n`. This is the complete "two scalar proximities
⟹ one quantified mutual proximate" statement — the correlated-agreement content
at the pairwise (`1−2δ`) level, the template the Johnson-regime apex sharpens. -/

namespace MCAJohnson

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)

/-- **Quantified joint agreement.** Given two degree-`<deg` proximates `c, c'` of
the affine line at distinct slopes `γ ≠ γ'`, with agreement sets `A` (for `c` at
`γ`) and `A'` (for `c'` at `γ'`), there is a degree-`<deg` codeword pair `(p₀,p₁)`
jointly interpolating `(f₀,f₁)` on `A ∩ A'`, and `|A ∩ A'| ≥ |A| + |A'| − n`. -/
theorem affineLine_joint_agreement {deg : ℕ}
    {c c' : F[X]} (hc : c ∈ Polynomial.degreeLT F deg)
    (hc' : c' ∈ Polynomial.degreeLT F deg)
    {γ γ' : F} (hγ : γ ≠ γ') {f₀ f₁ : ι → F}
    (A A' : Finset ι)
    (hA : ∀ x ∈ A, c.eval (domain x) = f₀ x + γ * f₁ x)
    (hA' : ∀ x ∈ A', c'.eval (domain x) = f₀ x + γ' * f₁ x) :
    ∃ (p₀ p₁ : F[X]) (S : Finset ι),
      p₀ ∈ Polynomial.degreeLT F deg ∧ p₁ ∈ Polynomial.degreeLT F deg ∧
      S = A ∩ A' ∧
      (Fintype.card ι : ℤ) ≥ (A.card : ℤ) + (A'.card : ℤ) - (S.card : ℤ) ∧
      (∀ x ∈ S, p₁.eval (domain x) = f₁ x ∧ p₀.eval (domain x) = f₀ x) := by
  classical
  -- extraction on the common agreement set S = A ∩ A'
  obtain ⟨p₀, p₁, hp₀, hp₁, hpe⟩ :=
    affineLine_mutual_extract domain hc hc' hγ
      (S := A ∩ A') (f₀ := f₀) (f₁ := f₁)
      (fun x hx => ⟨hA x (Finset.mem_inter.mp hx).1, hA' x (Finset.mem_inter.mp hx).2⟩)
  refine ⟨p₀, p₁, A ∩ A', hp₀, hp₁, rfl, ?_, hpe⟩
  -- inclusion–exclusion: |A| + |A'| = |A ∩ A'| + |A ∪ A'| ≤ |A ∩ A'| + n
  have hue : (A ∪ A').card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
  have hie : (A ∩ A').card + (A ∪ A').card = A.card + A'.card :=
    Finset.card_inter_add_card_union A A'
  omega

/-- Nat-valued form of `affineLine_joint_agreement`: the common agreement set
has the standard inclusion-exclusion lower bound `|A ∩ A'| + n ≥ |A| + |A'|`.
This is the form usually needed for threshold arithmetic. -/
theorem affineLine_joint_agreement_nat_card {deg : ℕ}
    {c c' : F[X]} (hc : c ∈ Polynomial.degreeLT F deg)
    (hc' : c' ∈ Polynomial.degreeLT F deg)
    {γ γ' : F} (hγ : γ ≠ γ') {f₀ f₁ : ι → F}
    (A A' : Finset ι)
    (hA : ∀ x ∈ A, c.eval (domain x) = f₀ x + γ * f₁ x)
    (hA' : ∀ x ∈ A', c'.eval (domain x) = f₀ x + γ' * f₁ x) :
    ∃ (p₀ p₁ : F[X]) (S : Finset ι),
      p₀ ∈ Polynomial.degreeLT F deg ∧ p₁ ∈ Polynomial.degreeLT F deg ∧
      S = A ∩ A' ∧
      A.card + A'.card ≤ S.card + Fintype.card ι ∧
      (∀ x ∈ S, p₁.eval (domain x) = f₁ x ∧ p₀.eval (domain x) = f₀ x) := by
  classical
  obtain ⟨p₀, p₁, hp₀, hp₁, hpe⟩ :=
    affineLine_mutual_extract domain hc hc' hγ
      (S := A ∩ A') (f₀ := f₀) (f₁ := f₁)
      (fun x hx => ⟨hA x (Finset.mem_inter.mp hx).1, hA' x (Finset.mem_inter.mp hx).2⟩)
  refine ⟨p₀, p₁, A ∩ A', hp₀, hp₁, rfl, ?_, hpe⟩
  have hue : (A ∪ A').card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hie : (A ∩ A').card + (A ∪ A').card = A.card + A'.card :=
    Finset.card_inter_add_card_union A A'
  omega

end MCAJohnson
