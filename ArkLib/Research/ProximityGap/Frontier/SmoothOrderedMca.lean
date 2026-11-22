/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence

/-! # Transport an ordered-coset MCA lower bound to any smooth coordinate order -/
set_option autoImplicit false
open scoped NNReal ENNReal
namespace ProximityGap.SmoothOrderedMca

/-- A bound on every geometric ordering of a coset holds for a supplied
smooth domain of the same length in its original coordinate order. -/
theorem transfer {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I]
    {n k : ℕ} [NeZero n] (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = n)
    (width : ℕ) [NeZero width] (radius : ℝ≥0) (bound : ℝ≥0∞)
    (ordered : ∀ (E : Fin n ↪ F) (u g : F), u ≠ 0 → orderOf g = n →
      (∀ i, E i = u*g^i.val) →
      bound ≤ epsMCA (F:=F) ((ReedSolomon.code E k : Set (Fin n → F)) ^⋈ (Fin width)) radius) :
    bound ≤ epsMCA (F:=F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin width)) radius := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have : Nonempty I := Fintype.card_pos_iff.mp (hn ▸ NeZero.pos n)
  obtain ⟨sites,hsite⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I sites
  have card : Nat.card H = n := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr sites, hn]
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have ho : orderOf g = n := hg.trans card
  have hfield : orderOf ((g.val : Fˣ) : F) = n := by
    rwa [orderOf_units, Subgroup.orderOf_coe]
  let powers : Fin (n) ≃ H := Equiv.ofBijective (fun j => g^j.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j hij => Fin.ext ((IsPrimitiveRoot.iff_orderOf.mpr ho).pow_inj i.isLt j.isLt hij),
        by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card]⟩)
  let e := powers.trans sites.symm
  let E := e.toEmbedding.trans D
  have he (i : Fin (n)) : E i = (ReedSolomon.Smooth.a D : F) * (g.val : F)^i.val := by
    change D (sites.symm (powers i)) = _
    rw [hsite, sites.apply_symm_apply]
    rfl
  have hcode (w : I → F) : w ∘ e ∈ ReedSolomon.code E k ↔ w ∈ ReedSolomon.code D k := by
    simp only [ReedSolomon.mem_code_iff_eval]
    constructor
    · rintro ⟨P,hP,heval⟩
      exact ⟨P,hP,fun i => by simpa [E,Function.comp_def] using heval (e.symm i)⟩
    · rintro ⟨P,hP,heval⟩
      exact ⟨P,hP,fun i => heval (e i)⟩
  have hm := ordered E _ _ (ReedSolomon.Smooth.a D).ne_zero hfield he
  rw [epsMCA_interleaved_eq, epsMCA_eq_mcaError] at hm ⊢
  rwa [CoreDefinitions.mcaError_comp_equiv _ _ _ e hcode] at hm

#print axioms transfer
end ProximityGap.SmoothOrderedMca
