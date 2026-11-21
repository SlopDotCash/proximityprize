/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientSupport
import ArkLib.ToMathlib.LinearAlgebra.Submodule.Union
import ArkLib.Research.ProximityGap.Frontier._TwoSidedCapstone

/-! # Simultaneous support rank test for affine-line MCA

Fix one support for each selected scalar. The folded interpolation equations cut out a linear
space of row pairs. All the non-joint conditions can hold simultaneously precisely when none of
the individual joint-agreement spaces contains that common space. There are at most as many
distinct scalars as field elements, including when all scalars are selected.
-/

open scoped NNReal ENNReal
open ProximityGap.ProjectiveQuotientSupport
namespace ProximityGap.SimultaneousSupportRank

variable {F I : Type} [Field F]

private abbrev W (I F : Type) := I → F

/-- Words admitting a codeword on the specified support. -/
def restrictedCode (C : Submodule F (I → F)) (S : Finset I) : Submodule F (I → F) :=
  (quotientSupportSubmodule C S).comap C.mkQ

/-- Row pairs whose affine fold at the selected scalar has a codeword on its support. -/
def foldSpace (C : Submodule F (I → F)) (S : Finset I) (c : F) :
    Submodule F ((I → F) × (I → F)) :=
  (restrictedCode C S).comap
    (LinearMap.fst F (W I F) (W I F) + c • LinearMap.snd F (W I F) (W I F))

/-- Row pairs satisfying every selected scalar's folded interpolation equations. -/
noncomputable def space (C : Submodule F (I → F)) (G : Finset F) (S : G → Finset I) :
    Submodule F ((I → F) × (I → F)) :=
  ⨅ g, foldSpace C (S g) g

/-- Row pairs admitting individual codewords on one common support. -/
def jointSpace (C : Submodule F (I → F)) (S : Finset I) :
    Submodule F ((I → F) × (I → F)) :=
  (restrictedCode C S).prod (restrictedCode C S)

section
variable [Finite F] [Finite I] [Nonempty I]

private theorem fold_iff (C : Submodule F (I → F)) (S : Finset I) (c : F)
    (x : (I → F) × (I → F)) :
    x ∈ foldSpace C S c ↔ ∃ w ∈ C, ∀ i ∈ S, w i = x.1 i + c • x.2 i := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite I
  exact quotient_mk_mem_quotientSupportSubmodule_iff C S (x.1 + c • x.2)

private theorem joint_iff (C : Submodule F (I → F)) (S : Finset I)
    (x : (I → F) × (I → F)) :
    x ∈ jointSpace C S ↔ pairJointAgreesOn (C : Set (I → F)) S x.1 x.2 := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite I
  exact (pairJointAgreesOn_iff_quotientSupport C S x.1 x.2).symm

end

variable [Fintype I] [Nonempty I]

/-- Prescribed scalars can be bad together iff each joint condition is proper on the same
folded solution space, for some sufficiently large witness support per scalar. -/
theorem simultaneous_iff [Finite F] (C : Submodule F (I → F)) (δ : ℝ≥0) (G : Finset F) :
    (∃ x : (I → F) × (I → F), ∀ g : G, mcaEvent (C : Set (I → F)) δ x.1 x.2 (g : F)) ↔
    ∃ S : G → Finset I, (∀ g, (S g).card ≥ (1 - δ) * Fintype.card I) ∧
      ∀ g, ¬space C G S ≤ jointSpace C (S g) := by
  classical
  let := Fintype.ofFinite F
  constructor
  · rintro ⟨x, hx⟩
    choose S hcard hfold hjoint using hx
    refine ⟨S, hcard, ?_⟩
    have hspace : x ∈ space C G S := (Submodule.mem_iInf _).mpr
      fun g => (fold_iff C (S g) g x).mpr (hfold g)
    exact fun g h => hjoint g ((joint_iff C (S g) x).mp (h hspace))
  · rintro ⟨S, hcard, hproper⟩
    let L := space C G S
    let J (g : G) := (jointSpace C (S g)).comap L.subtype
    have hne (g : G) : J g ≠ ⊤ := fun hg => hproper g (Submodule.comap_subtype_eq_top.mp hg)
    have hsize : (Finset.univ : Finset G).card ≤ Nat.card F := by
      simpa only [Finset.card_univ, Fintype.card_coe, Nat.card_eq_fintype_card] using G.card_le_univ
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_card_le
      (Finset.univ : Finset G) J (fun g _ => hne g) hsize
    have hspace : ∀ g : G, (x : (I → F) × (I → F)) ∈ foldSpace C (S g) g :=
      (Submodule.mem_iInf _).mp x.property
    exact ⟨x, fun g => ⟨S g, hcard g, (fold_iff C (S g) g x).mp (hspace g),
      fun hj => hx g (Finset.mem_univ _) ((joint_iff C (S g) x).mpr hj)⟩⟩

/-- In ordinary coordinates each strict dimension inequality means that appending the joint
constraints strictly increases the rank of the folded constraint matrix. -/
theorem simultaneous_rank [Finite F] (C : Submodule F (I → F)) (δ : ℝ≥0) (G : Finset F) :
    (∃ x : (I → F) × (I → F), ∀ g : G, mcaEvent (C : Set (I → F)) δ x.1 x.2 (g : F)) ↔
    ∃ S : G → Finset I, (∀ g, (S g).card ≥ (1 - δ) * Fintype.card I) ∧
      ∀ g, Module.finrank F ↥(space C G S ⊓ jointSpace C (S g)) <
        Module.finrank F (space C G S) := by
  rw [simultaneous_iff]
  apply exists_congr
  intro S
  apply and_congr_right
  intro _
  apply forall_congr'
  intro g
  constructor
  · intro h
    apply Submodule.finrank_lt_finrank_of_lt
    exact lt_of_le_of_ne inf_le_left (fun he => h (inf_eq_left.mp he))
  · intro h hle
    rw [inf_eq_left.mpr hle] at h
    exact lt_irrefl _ h

variable [Fintype F]

/-- Failure of an arbitrary integer error budget is equivalent to a rank-increase certificate
on a single family of supports indexed by exactly one more than the budgeted number of scalars. -/
theorem budget_failure_iff (C : Submodule F (I → F)) (δ : ℝ≥0) (B : ℕ) :
    (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) < epsMCA (F := F) (C : Set (I → F)) δ ↔
    ∃ (G : Finset F) (_ : G.card = B + 1) (S : G → Finset I),
      (∀ g, (S g).card ≥ (1 - δ) * Fintype.card I) ∧
      ∀ g, Module.finrank F ↥(space C G S ⊓ jointSpace C (S g)) <
        Module.finrank F (space C G S) := by
  classical
  rw [← not_le,
    ArkLib.ProximityGap.Frontier.TwoSidedCapstone.epsMCA_le_iff_worstCaseIncidenceBounded]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := not_forall.mp h
    let bad := Finset.univ.filter (fun c : F => mcaEvent (C : Set (I → F)) δ (u 0) (u 1) c)
    have hn : B + 1 ≤ bad.card := Nat.succ_le_of_lt (lt_of_not_ge hu)
    obtain ⟨G, hsub, hG⟩ := Finset.exists_subset_card_eq hn
    have hbad : ∀ g : G, mcaEvent (C : Set (I → F)) δ (u 0) (u 1) (g : F) :=
      fun g => (Finset.mem_filter.mp (hsub g.property)).2
    obtain ⟨S, hs⟩ := (simultaneous_rank C δ G).mp ⟨(u 0, u 1), hbad⟩
    exact ⟨G, hG, S, hs⟩
  · rintro ⟨G, hG, S, hsize, hdim⟩ h
    obtain ⟨x, hx⟩ := (simultaneous_rank C δ G).mpr ⟨S, hsize, hdim⟩
    let u : Code.WordStack F (Fin 2) I := ![x.1, x.2]
    have hsub : G ⊆ Finset.univ.filter (fun c : F => mcaEvent (C : Set (I → F)) δ (u 0) (u 1) c) :=
      fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx ⟨c, hc⟩⟩
    have hh := (Finset.card_le_card hsub).trans (h u)
    omega

/-- The same criterion in the canonical generator-indexed error used by the grand challenge. -/
theorem canonical_failure_iff [SampleableType F] (C : Submodule F (I → F)) (δ : ℝ≥0) (B : ℕ) :
    (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) <
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) C (δ : ℝ) ↔
    ∃ (G : Finset F) (_ : G.card = B + 1) (S : G → Finset I),
      (∀ g, (S g).card ≥ (1 - δ) * Fintype.card I) ∧
      ∀ g, Module.finrank F ↥(space C G S ⊓ jointSpace C (S g)) <
        Module.finrank F (space C G S) := by
  classical
  rw [← epsMCA_eq_mcaError]
  exact budget_failure_iff C δ B

/-- The permitted number of challenges is an integer even at an arbitrary real tolerance. -/
theorem epsMCA_le_iff_floor_budget (C : Set (I → F)) (δ ε : ℝ≥0) :
    epsMCA (F := F) C δ ≤ (ε : ℝ≥0∞) ↔
      epsMCA (F := F) C δ ≤ (⌊ε * Fintype.card F⌋₊ : ℝ≥0∞) / Fintype.card F := by
  classical
  constructor
  · intro h
    apply (ArkLib.ProximityGap.Frontier.TwoSidedCapstone.epsMCA_le_iff_worstCaseIncidenceBounded
      C δ ⌊ε * Fintype.card F⌋₊).mpr
    intro u
    apply Nat.le_floor
    have hcount := ProximityGap.OpenCoreConverse.incidence_le_of_epsMCA_le
      (F := F) C (ε : ℝ≥0∞) h u
    rw [mul_comm] at hcount
    exact_mod_cast hcount
  · intro h
    apply h.trans
    rw [ENNReal.div_le_iff (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)]
    have he := Nat.floor_le (show 0 ≤ ε * Fintype.card F by positivity)
    exact_mod_cast he

#print axioms epsMCA_le_iff_floor_budget
#print axioms canonical_failure_iff
#print axioms budget_failure_iff
#print axioms simultaneous_iff
#print axioms simultaneous_rank
end ProximityGap.SimultaneousSupportRank
