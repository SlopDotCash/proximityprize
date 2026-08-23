/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungMaximalFrame

/-!
# The sharpened per-class cap (#371, rung): `(n−|A|)/(t−|A|)`

The loose `n − |A|` cap (`maximal_frame_attached_card_le`) is improved using
the WITNESS-SIZE floor.  A class-`i` bad scalar has a witness `S` of size
`≥ t`, so its off-part `S \ A` has size `≥ t − |A|` (since `|S ∩ A| ≤ |A|`).
With off-parts pairwise disjoint (maximal frame), the multiplicity-refined
reservoir count `disjoint_offparts_card_mul_le` gives

  `(t − |A|) · #Γ ≤ n − |A|`,  i.e.  `#Γ ≤ (n − |A|)/(t − |A|)`.

At the rung (`n = 16`, `t = 7`): a size-5 class caps at `11/2 → 5` (not 11),
size-4 at `12/3 = 4`, size-3 at `13/4 → 3`.  This closes the small-class
gap that the constructive probe `probe_wb371_construct3` exposed (3 disjoint
size-5 classes realize ≈1, the loose cap gave 33; the sharp cap gives ≤ 15).
Size-6 classes (`t − |A| = 1`) still cap at `n − |A| = 10` — those need the
shared-R₀ coupling, not this count.
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section SharpCap

variable {dom : Fin n ↪ F} {R₀' R₁ q h : F[X]}

/-- **The sharpened per-class cap**: class scalars whose witnesses have size
`≥ t` and leave a maximal agreement set `A` (`t > |A|`) number at most
`(n − |A|)/(t − |A|)` — in the multiplicative form `(t−|A|)·#Γ ≤ n−|A|`. -/
theorem maximal_frame_attached_card_mul_le
    {Γ : Finset F} {A : Finset (Fin n)} {t : ℕ}
    (S : F → Finset (Fin n)) (g : F → F[X])
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h)
    (hid : ∀ γ ∈ Γ, R₀' + C γ * (vanishingPoly dom A * h)
      = g γ * vanishingPoly dom (S γ))
    (hwit : ∀ γ ∈ Γ, t ≤ (S γ).card) :
    (t - A.card) * Γ.card ≤ n - A.card := by
  classical
  have hres := disjoint_offparts_card_mul_le (m := t - A.card)
    (Γ := Γ) (W := (Finset.univ \ A : Finset (Fin n)))
    (off := fun γ => S γ \ A) ?_ ?_ ?_
  · rwa [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A),
      Finset.card_univ, Fintype.card_fin] at hres
  · -- off-parts land in the complement
    intro γ _ i hi
    rw [Finset.mem_sdiff] at hi ⊢
    exact ⟨Finset.mem_univ i, hi.2⟩
  · -- off-part size ≥ t − |A|
    intro γ hγ
    show t - A.card ≤ (S γ \ A).card
    have hsub : (S γ ∩ A).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsplit : (S γ ∩ A).card + (S γ \ A).card = (S γ).card :=
      Finset.card_inter_add_card_sdiff _ _
    have := hwit γ hγ
    omega
  · -- pairwise disjoint off-parts (maximal frame)
    intro γ₁ h₁ γ₂ h₂ hne
    exact maximal_frame_offparts_disjoint hne hA hfac (hid γ₁ h₁) (hid γ₂ h₂)

end SharpCap

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.maximal_frame_attached_card_mul_le
