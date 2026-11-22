/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Research.ProximityGap.Frontier.LocatorPadding

/-!
# Extending a Reed–Solomon MCA witness by zero coordinates

Multiplying both received rows and their decoded polynomial by the locator of the new
coordinates preserves every old bad scalar. A joint explanation on the enlarged witness
must vanish at each new point, so division by the locator recovers a joint explanation
on the original witness.
-/

open Finset Polynomial ProximityGap
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.RSLocatorExtension

variable {F : Type} [Field F] {n N k : ℕ}

/-- New coordinates, indexed in the enlarged evaluation domain. -/
def fresh (old : Fin n ↪ Fin N) : Finset (Fin N) :=
  (Finset.univ.map old)ᶜ

private theorem fresh_card (old : Fin n ↪ Fin N) : (fresh old).card = N - n := by
  simp [fresh, Finset.card_compl]

private theorem old_not_fresh (old : Fin n ↪ Fin N) (i : Fin n) : old i ∉ fresh old := by
  intro hi
  exact (Finset.mem_compl.mp hi) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- The monic polynomial whose simple roots are the new evaluation points. -/
noncomputable def locator (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) : F[X] :=
  Lagrange.nodal (fresh old) dom

variable [NeZero n]

/-- Evaluate the locator times the old word on the old domain and zero on all new points. -/
noncomputable def extendWord (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) (u : Fin n → F)
    (j : Fin N) : F :=
  (locator old dom).eval (dom j) * u (Function.invFun old j)

/-- Every bad scalar remains bad after locator extension, provided the new cardinality
threshold admits the old witness together with every new coordinate. -/
theorem mcaEvent_extend (old : Fin n ↪ Fin N) (dom : Fin N ↪ F) (hk : 0 < k)
    {δ δ' : ℝ≥0} (hsize : ∀ a : ℕ,
      (1 - δ) * n ≤ (a : ℝ≥0) → (1 - δ') * N ≤ ((a + (N - n) : ℕ) : ℝ≥0))
    (u₀ u₁ : Fin n → F) (γ : F)
    (hbad : mcaEvent (ReedSolomon.code (old.trans dom) k : Set (Fin n → F)) δ u₀ u₁ γ) :
    mcaEvent (ReedSolomon.code dom (k + (N - n)) : Set (Fin N → F)) δ'
      (extendWord old dom u₀) (extendWord old dom u₁) γ := by
  have cap : ∀ t : ℕ, (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (t : ℝ≥0) →
      (1 - δ') * (Fintype.card (Fin N) : ℝ≥0) ≤ ((t + (fresh old).card : ℕ) : ℝ≥0) := by
    simpa only [Fintype.card_fin, fresh_card] using hsize
  have lifted := LocatorPadding.mcaEvent_extend old dom (fresh old) (old_not_fresh old)
    hk cap u₀ u₁ γ hbad
  have words (u : Fin n → F) : LocatorPadding.extendWord old dom (fresh old) u =
      extendWord old dom u := by
    funext i
    rfl
  simpa only [fresh_card, words] using lifted

open Classical in
/-- The inclusion of bad scalars for a fixed pair of received words as a count. -/
theorem badScalar_card_le_extension [Fintype F] (old : Fin n ↪ Fin N) (dom : Fin N ↪ F)
    (hk : 0 < k) {δ δ' : ℝ≥0} (hsize : ∀ a : ℕ,
      (1 - δ) * n ≤ (a : ℝ≥0) → (1 - δ') * N ≤ ((a + (N - n) : ℕ) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter fun γ : F =>
      mcaEvent (ReedSolomon.code (old.trans dom) k : Set (Fin n → F)) δ u₀ u₁ γ).card ≤
    (Finset.univ.filter fun γ : F =>
      mcaEvent (ReedSolomon.code dom (k + (N - n)) : Set (Fin N → F)) δ'
        (extendWord old dom u₀) (extendWord old dom u₁) γ).card := by
  apply Finset.card_le_card
  intro γ hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    mcaEvent_extend old dom hk hsize u₀ u₁ γ (Finset.mem_filter.mp hγ).2⟩

end ArkLib.ProximityGap.Frontier.RSLocatorExtension

#print axioms ArkLib.ProximityGap.Frontier.RSLocatorExtension.mcaEvent_extend

#print axioms ArkLib.ProximityGap.Frontier.RSLocatorExtension.badScalar_card_le_extension
