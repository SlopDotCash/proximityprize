/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungTripleRelation

/-!
# Maximal-frame reservoir (#371, rung): the exact per-frame cap `n − |A|`

The scope-corrected ledger inflated the per-(A, frame) reservoir to
`(n−|A|) + deg h` because `frame_cross_disjoint` lets distinct attached
witnesses also meet at domain roots of `h`.  This file closes that leak:
when `A` is the FULL (maximal) agreement set of the direction row with its
frame polynomial — `i ∈ A ↔ R₁(xᵢ) = q(xᵢ)` — the factor `h` cannot vanish
anywhere on the domain off `A` (a root would put the point IN `A`).  Hence:

* `maximal_agreement_offA_no_root` — off `A`, `h` has no domain roots;
* `maximal_frame_offparts_disjoint` — same-frame attached witnesses are
  pairwise disjoint off `A`, with no `h`-escape;
* `maximal_frame_attached_card_le` — per (maximal `A`, frame): at most
  `n − |A|` attached scalars with witnesses leaving `A`;
* `disjoint_offparts_card_mul_le` — the multiplicity-refined reservoir
  count: off-parts of size ≥ `m` give `m · #Γ ≤ |reservoir|`.

Probe-exact at the pencil: `|A| = 8`, 8 attached per half-coset, perfect
matching (`probe_wb371_rung_offA`: singletons, bijective, 0 violations).
-/

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section MaximalFrame

variable {dom : Fin n ↪ F} {R₀' R₁ q h : F[X]}

/-- **No `h`-roots off a maximal agreement set**: if `A` is the full
agreement locus of `R₁` with `q` and `R₁ − q = m_A·h`, then `h` has no
domain roots outside `A`. -/
theorem maximal_agreement_offA_no_root {A : Finset (Fin n)}
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h) :
    ∀ i, i ∉ A → h.eval (dom i) ≠ 0 := by
  intro i hiA hh
  have hev := congrArg (Polynomial.eval (dom i)) hfac
  rw [eval_sub, eval_mul, hh, mul_zero, sub_eq_zero] at hev
  exact hiA ((hA i).mpr hev)

/-- **Same-frame off-part disjointness, maximal form**: witnesses of
distinct scalars attached to a maximal agreement set with a common frame
are pairwise disjoint off `A` — no `h`-locus escape. -/
theorem maximal_frame_offparts_disjoint
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {g₁ g₂ : F[X]} {A S₁ S₂ : Finset (Fin n)}
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h)
    (hid₁ : R₀' + C γ₁ * (vanishingPoly dom A * h)
      = g₁ * vanishingPoly dom S₁)
    (hid₂ : R₀' + C γ₂ * (vanishingPoly dom A * h)
      = g₂ * vanishingPoly dom S₂) :
    Disjoint (S₁ \ A) (S₂ \ A) := by
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  rw [Finset.mem_sdiff] at hi₁ hi₂
  have hcross := frame_cross_disjoint hne hid₁ hid₂ i
    (Finset.mem_inter.mpr ⟨hi₁.1, hi₂.1⟩)
  rcases hcross with hiA | hroot
  · exact hi₁.2 hiA
  · exact maximal_agreement_offA_no_root hA hfac i hi₁.2 hroot

/-- **The multiplicity-refined reservoir count**: pairwise-disjoint
off-parts of size at least `m` inside a reservoir `W` cap the family at
`m · #Γ ≤ #W`. -/
theorem disjoint_offparts_card_mul_le {m : ℕ} {Γ : Finset F}
    {W : Finset (Fin n)} (off : F → Finset (Fin n))
    (hsub : ∀ γ ∈ Γ, off γ ⊆ W)
    (hm : ∀ γ ∈ Γ, m ≤ (off γ).card)
    (hdisj : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → Disjoint (off γ₁) (off γ₂)) :
    m * Γ.card ≤ W.card := by
  classical
  have hcard : m * Γ.card ≤ (Γ.biUnion off).card := by
    rw [Finset.card_biUnion hdisj]
    calc m * Γ.card = ∑ _γ ∈ Γ, m := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ γ ∈ Γ, (off γ).card := Finset.sum_le_sum hm
  refine le_trans hcard (Finset.card_le_card ?_)
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨γ, hγ, hxγ⟩ := hx
  exact hsub γ hγ hxγ

/-- **The maximal-frame cap**: scalars attached to a maximal agreement set
`A` through a common frame, each with a witness leaving `A`, number at most
`n − |A|`. -/
theorem maximal_frame_attached_card_le
    {Γ : Finset F} {A : Finset (Fin n)}
    (S : F → Finset (Fin n)) (g : F → F[X])
    (hA : ∀ i, i ∈ A ↔ R₁.eval (dom i) = q.eval (dom i))
    (hfac : R₁ - q = vanishingPoly dom A * h)
    (hid : ∀ γ ∈ Γ, R₀' + C γ * (vanishingPoly dom A * h)
      = g γ * vanishingPoly dom (S γ))
    (hleave : ∀ γ ∈ Γ, ((S γ) \ A).Nonempty) :
    Γ.card ≤ n - A.card := by
  classical
  have hres : Γ.card ≤ (Finset.univ \ A : Finset (Fin n)).card := by
    refine disjoint_offparts_card_le (fun γ => S γ \ A) ?_ hleave ?_
    · intro γ _ i hi
      rw [Finset.mem_sdiff] at hi ⊢
      exact ⟨Finset.mem_univ i, hi.2⟩
    · intro γ₁ h₁ γ₂ h₂ hne
      exact maximal_frame_offparts_disjoint hne hA hfac
        (hid γ₁ h₁) (hid γ₂ h₂)
  rwa [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A),
    Finset.card_univ, Fintype.card_fin] at hres

end MaximalFrame

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.maximal_agreement_offA_no_root
#print axioms ProximityGap.WBPencil.maximal_frame_offparts_disjoint
#print axioms ProximityGap.WBPencil.disjoint_offparts_card_mul_le
#print axioms ProximityGap.WBPencil.maximal_frame_attached_card_le
