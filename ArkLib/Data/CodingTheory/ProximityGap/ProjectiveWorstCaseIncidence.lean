/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAProjectiveEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# The production incidence core is exactly projective

`WorstCaseIncidenceBounded C delta E` counts bad scalars in one affine chart of each
two-row pencil.  `MCAProjectiveEquivariance` shows that the pencil itself has `|F| + 1`
projective slots and that a general invertible row mix moves the omitted infinity slot.
The affine decomposition therefore appears to lose one bad slot.

For the production regime `E < |F|`, the universal quantifier over stacks removes that loss
exactly.  If infinity is bad, the affine count is still strictly below `|F|`, so some affine
slot `gamma` is good.  The row mix

`(u0, u1) |-> (u1, u0 + gamma*u1)`

moves that good slot to infinity.  Its action on projective slots is the explicit equivalence
`rebaseSlotEquiv`; hence the projective bad count is unchanged, while the new affine count is
the whole projective count.

In the linear-code, finite-field setting of this module, the headline theorem
`worstCaseIncidenceBounded_iff_projective` proves

`WorstCaseIncidenceBounded C delta E <-> forall u, badSlotCount C delta u0 u1 <= E`

with the additional numeric hypothesis `E < |F|`.  The right side is a projective census, and
`MCAProjectiveEquivariance` proves its invariance under every invertible row mix.  The explicit
rebase below is the chart change needed to move away from a bad infinity slot.  The final
consumers feed the census directly into the existing operational `mcaDeltaStar` floor engine.
This does not prove the incidence bound; it removes the affine-chart artifact and identifies
the exact GL2-invariant projective object a production proof must bound.  The quotient-rank
reduction below also proves that rank-zero and rank-one pencils have at most one bad slot, so
every production budget `E >= 1` only needs genuine rank-two quotient pencils.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.ProjectiveWorstCaseIncidence

open ProximityGap.MCAProjectiveEquivariance
open ProximityGap.MCAEquivariance
open ProximityGap.OpenCoreConditionalPin

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The projective reparametrization induced by the row mix
`(u0,u1) |-> (u1,u0+gamma*u1)`. -/
def rebaseSlotEquiv (γ : F) : Option F ≃ Option F where
  toFun
    | none => some γ
    | some t => if t = 0 then none else some (t⁻¹ + γ)
  invFun
    | none => some 0
    | some s => if s = γ then none else some ((s - γ)⁻¹)
  left_inv := by
    intro s
    rcases s with _ | t
    · simp
    · by_cases ht : t = 0
      · simp [ht]
      · simp [ht]
  right_inv := by
    intro s
    rcases s with _ | t
    · simp
    · by_cases ht : t = γ
      · simp [ht]
      · have hsub : t - γ ≠ 0 := sub_ne_zero.mpr ht
        simp [ht, hsub]

/-- Rebasing sends the chosen affine slot `gamma` exactly to infinity. -/
theorem mcaEventProj_rebase_infty (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) :
    mcaEventProj (F := F) (C : Set (ι → A)) δ u₁ (u₀ + γ • u₁) 0 1 ↔
      mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ 1 γ := by
  simpa using
    (mcaEventProj_row_mix C (a := (0 : F)) (b := 1) (c := 1) (d := γ)
      (by simp) δ u₀ u₁ 0 1)

/-- The projective bad-slot predicate transports through the explicit rebase equivalence. -/
theorem badSlot_rebase_iff (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) (s : Option F) :
    badSlot (F := F) (C : Set (ι → A)) δ u₁ (u₀ + γ • u₁) s ↔
      badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ (rebaseSlotEquiv γ s) := by
  rcases s with _ | t
  · simpa [badSlot, slotCoords, rebaseSlotEquiv] using
      mcaEventProj_rebase_infty C δ u₀ u₁ γ
  · by_cases ht : t = 0
    · subst t
      simpa [badSlot, slotCoords, rebaseSlotEquiv] using
        (mcaEventProj_row_mix C (a := (0 : F)) (b := 1) (c := 1) (d := γ)
          (by simp) δ u₀ u₁ 1 0)
    · have hrow :=
        mcaEventProj_row_mix C (a := (0 : F)) (b := 1) (c := 1) (d := γ)
          (by simp) δ u₀ u₁ 1 t
      have hscale := mcaEventProj_smul C ht δ u₀ u₁ 1 (t⁻¹ + γ)
      have hrow' :
          mcaEventProj (F := F) (C : Set (ι → A)) δ u₁ (u₀ + γ • u₁) 1 t ↔
            mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ t (1 + t * γ) := by
        simpa using hrow
      have hscale' :
          mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ t (1 + t * γ) ↔
            mcaEventProj (F := F) (C : Set (ι → A)) δ u₀ u₁ 1 (t⁻¹ + γ) := by
        simpa [mul_add, mul_inv_cancel₀ ht] using hscale
      simpa [badSlot, slotCoords, rebaseSlotEquiv, ht] using hrow'.trans hscale'

/-- The projective census, unlike the affine census, is invariant under the rebase. -/
theorem badSlotCount_rebase (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₁ (u₀ + γ • u₁) =
      badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ := by
  simpa using
    (badSlotCount_row_mix C (a := (0 : F)) (b := 1) (c := 1) (d := γ)
      (by simp) δ u₀ u₁)

/-- The projective form of the all-stack production incidence budget. -/
def ProjectiveWorstCaseIncidenceBounded
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι,
    badSlotCount (F := F) (C : Set (ι → A)) δ (u 0) (u 1) ≤ E

/-- **The affine and projective production cores are exactly equivalent below the full-field
budget.**  The universal stack quantifier lets any good affine slot be moved to infinity,
eliminating the apparent `+1` chart loss. -/
theorem worstCaseIncidenceBounded_iff_projective
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ)
    (hE : E < Fintype.card F) :
    WorstCaseIncidenceBounded (F := F) (A := A) (C : Set (ι → A)) δ E ↔
      ProjectiveWorstCaseIncidenceBounded C δ E := by
  classical
  constructor
  · intro hI u
    by_cases hinf :
        mcaEventProj (F := F) (C : Set (ι → A)) δ (u 0) (u 1) 0 1
    · let B : Finset F := Finset.univ.filter (fun γ : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      have hB : B.card ≤ E := by
        simpa [B] using hI u
      have hBlt : B.card < (Finset.univ : Finset F).card := by
        simpa using lt_of_le_of_lt hB hE
      obtain ⟨γ, _hγuniv, hγB⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hBlt
      have hγgood :
          ¬ mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ := by
        intro hbad
        exact hγB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩)
      let v : WordStack A (Fin 2) ι := ![u 1, u 0 + γ • u 1]
      have hv : (Finset.univ.filter (fun z : F =>
          mcaEvent (F := F) (C : Set (ι → A)) δ (v 0) (v 1) z)).card ≤ E :=
        hI v
      have hvinf :
          ¬ mcaEventProj (F := F) (C : Set (ι → A)) δ (v 0) (v 1) 0 1 := by
        intro hbad
        apply hγgood
        exact (mcaEventProj_one_gamma
          (C : Set (ι → A)) δ (u 0) (u 1) γ).mp
          ((mcaEventProj_rebase_infty C δ (u 0) (u 1) γ).mp
            (by simpa [v] using hbad))
      have hvdecomp := badSlotCount_eq_affine_add_infty
        (F := F) (C : Set (ι → A)) δ (v 0) (v 1)
      have hPeq := badSlotCount_rebase C δ (u 0) (u 1) γ
      calc
        badSlotCount (F := F) (C : Set (ι → A)) δ (u 0) (u 1) =
            badSlotCount (F := F) (C : Set (ι → A)) δ (v 0) (v 1) := by
              simpa [v] using hPeq.symm
        _ = (Finset.univ.filter (fun z : F =>
            mcaEvent (F := F) (C : Set (ι → A)) δ (v 0) (v 1) z)).card := by
              simpa [if_neg hvinf] using hvdecomp
        _ ≤ E := hv
    · have hdecomp := badSlotCount_eq_affine_add_infty
        (F := F) (C : Set (ι → A)) δ (u 0) (u 1)
      rw [if_neg hinf] at hdecomp
      rw [hdecomp]
      exact hI u
  · intro hP u
    have hdecomp := badSlotCount_eq_affine_add_infty
      (F := F) (C : Set (ι → A)) δ (u 0) (u 1)
    have hle := hP u
    omega

/-- The MCA error budget is itself equivalent to the projective all-stack budget. -/
theorem epsMCA_le_iff_projective
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ)
    (hE : E < Fintype.card F) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
        ≤ (E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ↔
      ProjectiveWorstCaseIncidenceBounded C δ E := by
  classical
  constructor
  · intro heps
    apply (worstCaseIncidenceBounded_iff_projective C δ E hE).mp
    intro u
    have hstack : ((Finset.univ.filter
          (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ
            (u 0) (u 1) γ)).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞)
        ≤ (E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
      refine le_trans ?_ heps
      have hprob :
          Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ
            (u 0) (u 1) γ]
            = ((Finset.univ.filter
                (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ
                  (u 0) (u 1) γ)).card : ℝ≥0∞)
              / (Fintype.card F : ℝ≥0∞) :=
        prob_uniform_eq_card_filter_div_card _
      calc
        ((Finset.univ.filter
            (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ
              (u 0) (u 1) γ)).card : ℝ≥0∞)
            / (Fintype.card F : ℝ≥0∞)
          = Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (C : Set (ι → A)) δ
              (u 0) (u 1) γ] := hprob.symm
        _ ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ :=
          mcaEvent_prob_le_epsMCA (F := F) (A := A) (C : Set (ι → A)) δ u
    have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    have hqtop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hle : ((Finset.univ.filter
          (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ
            (u 0) (u 1) γ)).card : ℝ≥0∞) ≤ (E : ℝ≥0∞) := by
      rw [ENNReal.div_le_iff_le_mul (Or.inl hq0) (Or.inl hqtop)] at hstack
      rwa [ENNReal.div_mul_cancel hq0 hqtop] at hstack
    exact_mod_cast hle
  · intro hP
    exact epsMCA_le_of_worstCaseIncidence (F := F) (A := A)
      (C : Set (ι → A)) δ
      ((worstCaseIncidenceBounded_iff_projective C δ E hE).mpr hP)

/-- A projective incidence budget gives the operational `deltaStar` floor directly. -/
theorem projectiveWorstCaseIncidence_pin
    (C : Submodule F (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {E : ℕ}
    (hδ : δ ≤ 1) (hE : E < Fintype.card F)
    (hP : ProjectiveWorstCaseIncidenceBounded C δ E)
    (hbudget : (E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := A) (C : Set (ι → A)) εstar := by
  exact worstCaseIncidence_pin (F := F) (A := A) (C : Set (ι → A)) εstar hδ
    ((worstCaseIncidenceBounded_iff_projective C δ E hE).mpr hP) hbudget

/-- Budget-ratio specialization of `projectiveWorstCaseIncidence_pin`. -/
theorem projectiveWorstCaseIncidence_pin_budget
    (C : Submodule F (ι → A)) {δ : ℝ≥0} {E : ℕ}
    (hδ : δ ≤ 1) (hE : E < Fintype.card F)
    (hP : ProjectiveWorstCaseIncidenceBounded C δ E) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) (C : Set (ι → A))
      ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) := by
  exact projectiveWorstCaseIncidence_pin C _ hδ hE hP le_rfl

/-- **Exact operational pin from the first projective-budget failure.**  If every radius
strictly below `delta0` satisfies the projective census budget and `delta0` itself does not,
then the operational threshold at budget `E/|F|` is exactly `delta0`. -/
theorem mcaDeltaStar_eq_of_projective_jump
    (C : Submodule F (ι → A)) {E : ℕ} {δ₀ : ℝ≥0}
    (hE : E < Fintype.card F) (hδ₀ : δ₀ ≤ 1)
    (hgood : ∀ δ : ℝ≥0, δ < δ₀ → ProjectiveWorstCaseIncidenceBounded C δ E)
    (hbad : ¬ ProjectiveWorstCaseIncidenceBounded C δ₀ E) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) (C : Set (ι → A))
        ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) = δ₀ := by
  refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump
    (F := F) (A := A) (C : Set (ι → A)) _ hδ₀ ?_ ?_
  · intro δ hδ
    exact (epsMCA_le_iff_projective C δ E hE).mpr (hgood δ hδ)
  · apply lt_of_not_ge
    intro heps
    exact hbad ((epsMCA_le_iff_projective C δ₀ E hE).mp heps)

/-! ## Quotient-rank stratification -/

/-- A nontrivial linear combination of the rows is a codeword, equivalently their quotient
classes span a subspace of dimension at most one. -/
def RowsDependentModCode (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) : Prop :=
  ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a • u₀ + b • u₁ ∈ C

/-- A pair represents a genuine rank-two pencil in the quotient by `C`. -/
def RowsIndependentModCode (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) : Prop :=
  ¬ RowsDependentModCode C u₀ u₁

/-- If the direction row is a codeword, no affine slot can be bad. -/
theorem not_mcaEvent_of_right_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (hu₁ : u₁ ∈ C) (γ : F) :
    ¬ mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ := by
  intro hbad
  have htrans := mcaEvent_translate C C.zero_mem (C.neg_mem hu₁) (δ := δ)
    (u₀ := u₀) (u₁ := u₁) γ
  have hzero :
      mcaEvent (F := F) (C : Set (ι → A)) δ u₀ (0 : ι → A) γ := by
    apply htrans.mpr at hbad
    simpa using hbad
  obtain ⟨S, _hS, ⟨w, hw, hagree⟩, hno⟩ := hzero
  apply hno
  refine ⟨w, hw, 0, C.zero_mem, fun i hi => ⟨?_, rfl⟩⟩
  simpa using hagree i hi

/-- A pencil with a codeword direction has at most its infinity slot bad. -/
theorem badSlotCount_le_one_of_right_mem (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (hu₁ : u₁ ∈ C) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ 1 := by
  classical
  rw [badSlotCount_eq_affine_add_infty]
  have hcard :
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro γ _hγ
    exact not_mcaEvent_of_right_mem C δ u₀ u₁ hu₁ γ
  rw [hcard, zero_add]
  split <;> simp

/-- Linear dependence of the two quotient classes forces at most one bad projective slot. -/
theorem badSlotCount_le_one_of_rowsDependentModCode
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hdep : RowsDependentModCode C u₀ u₁) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ 1 := by
  obtain ⟨a, b, ha | hb, habC⟩ := hdep
  · have hdet : (0 : F) * b - 1 * a ≠ 0 := by simpa using ha
    have hmix := badSlotCount_row_mix C hdet δ u₀ u₁
    rw [← hmix]
    simpa using badSlotCount_le_one_of_right_mem C δ
      u₁ (a • u₀ + b • u₁) habC
  · have hdet : (1 : F) * b - 0 * a ≠ 0 := by simpa using hb
    have hmix := badSlotCount_row_mix C hdet δ u₀ u₁
    rw [← hmix]
    simpa using badSlotCount_le_one_of_right_mem C δ
      u₀ (a • u₀ + b • u₁) habC

/-- For budgets at least one, the all-stack projective condition only needs to be checked on
genuine rank-two quotient pencils. -/
theorem projectiveWorstCaseIncidenceBounded_iff_rankTwo
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) (hE : 1 ≤ E) :
    ProjectiveWorstCaseIncidenceBounded C δ E ↔
      ∀ u : WordStack A (Fin 2) ι,
        RowsIndependentModCode C (u 0) (u 1) →
          badSlotCount (F := F) (C : Set (ι → A)) δ (u 0) (u 1) ≤ E := by
  constructor
  · intro h u _hu
    exact h u
  · intro h u
    by_cases hdep : RowsDependentModCode C (u 0) (u 1)
    · exact le_trans
        (badSlotCount_le_one_of_rowsDependentModCode C δ (u 0) (u 1) hdep) hE
    · exact h u hdep

end ProximityGap.ProjectiveWorstCaseIncidence

/-! ## Axiom audit -/
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.mcaEventProj_rebase_infty
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.badSlot_rebase_iff
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.badSlotCount_rebase
#print axioms
  ProximityGap.ProjectiveWorstCaseIncidence.worstCaseIncidenceBounded_iff_projective
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.epsMCA_le_iff_projective
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.projectiveWorstCaseIncidence_pin
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.projectiveWorstCaseIncidence_pin_budget
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.mcaDeltaStar_eq_of_projective_jump
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.not_mcaEvent_of_right_mem
#print axioms ProximityGap.ProjectiveWorstCaseIncidence.badSlotCount_le_one_of_right_mem
#print axioms
  ProximityGap.ProjectiveWorstCaseIncidence.badSlotCount_le_one_of_rowsDependentModCode
#print axioms
  ProximityGap.ProjectiveWorstCaseIncidence.projectiveWorstCaseIncidenceBounded_iff_rankTwo

/-! ## Sharpness of the strict budget hypothesis

Over `F_2`, the zero code on three coordinates at radius `2/3` has a row pair whose three
projective slots are all bad.  At the full-field budget `E = |F_2| = 2`, every affine census
is nevertheless at most two by cardinality.  Thus `E < |F|` in the headline equivalence is
sharp, not a proof artifact.
-/

attribute [local instance] Classical.propDecidable

namespace ProximityGap.ProjectiveWorstCaseIncidenceBoundary

open ProximityGap.MCAProjectiveEquivariance
open ProximityGap.OpenCoreConditionalPin
open ProximityGap.ProjectiveWorstCaseIncidence

abbrev F2 := ZMod 2
abbrev I3 := Fin 3

def zeroCode : Submodule F2 (I3 → F2) := ⊥

def u0 : I3 → F2 := ![0, 1, 1]
def u1 : I3 → F2 := ![1, 0, 1]

noncomputable def delta : ℝ≥0 := 2 / 3

private theorem singleton_meets_radius :
    (1 - delta) * Fintype.card I3 ≤ (1 : ℝ≥0) := by
  change ((1 - 2 / 3) * 3 : ℝ≥0) ≤ 1
  have h : (2 / 3 : ℝ≥0) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 3)]
    norm_num
  have hsub : (1 - 2 / 3 : ℝ≥0) = 1 / 3 := by
    apply NNReal.eq
    rw [NNReal.coe_sub h]
    norm_num
  rw [hsub]
  norm_num

private theorem notJoint_zeroCode (i : I3) (hi0 : u0 i ≠ 0 ∨ u1 i ≠ 0) :
    ¬ pairJointAgreesOn (zeroCode : Set (I3 → F2)) {i} u0 u1 := by
  intro h
  obtain ⟨v0, hv0, v1, hv1, hag⟩ := h
  have hv0z : v0 = 0 := by simpa [zeroCode] using hv0
  have hv1z : v1 = 0 := by simpa [zeroCode] using hv1
  subst v0
  subst v1
  have hi := hag i (by simp)
  rcases hi0 with h0 | h1
  · exact h0 (by simpa using hi.1.symm)
  · exact h1 (by simpa using hi.2.symm)

private theorem bad_zero :
    mcaEventProj (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 1 0 := by
  refine ⟨{0}, ?_, ?_, notJoint_zeroCode 0 ?_⟩
  · simpa using singleton_meets_radius
  · refine ⟨0, by simp [zeroCode], ?_⟩
    intro i hi
    have hi' : i = 0 := by simpa using hi
    subst i
    simp [u0, u1]
  · right
    simp [u1]

private theorem bad_one :
    mcaEventProj (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 1 1 := by
  refine ⟨{2}, ?_, ?_, notJoint_zeroCode 2 ?_⟩
  · simpa using singleton_meets_radius
  · refine ⟨0, by simp [zeroCode], ?_⟩
    intro i hi
    have hi' : i = 2 := by simpa using hi
    subst i
    change (0 : F2) = 1 + 1
    decide
  · left
    simp [u0]

private theorem bad_infty :
    mcaEventProj (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 0 1 := by
  refine ⟨{1}, ?_, ?_, notJoint_zeroCode 1 ?_⟩
  · simpa using singleton_meets_radius
  · refine ⟨0, by simp [zeroCode], ?_⟩
    intro i hi
    have hi' : i = 1 := by simpa using hi
    subst i
    simp [u0, u1]
  · left
    simp [u0]

private theorem every_affine_bad (γ : F2) :
    mcaEvent (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 γ := by
  fin_cases γ
  · exact (mcaEventProj_one_gamma
      (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 0).mp bad_zero
  · exact (mcaEventProj_one_gamma
      (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 1).mp bad_one

private theorem affine_count_eq_two :
    (Finset.univ.filter (fun γ : F2 =>
      mcaEvent (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 γ)).card = 2 := by
  rw [Finset.filter_eq_self.mpr]
  · simp
  · intro γ _hγ
    exact every_affine_bad γ

/-- The selected pencil has all three projective slots bad. -/
theorem projective_count_eq_three :
    badSlotCount (F := F2) (zeroCode : Set (I3 → F2)) delta u0 u1 = 3 := by
  rw [badSlotCount_eq_affine_add_infty, affine_count_eq_two, if_pos bad_infty]

/-- At the full-field budget, the affine condition holds for every stack by cardinality. -/
theorem affine_boundary_holds :
    WorstCaseIncidenceBounded (F := F2) (A := F2)
      (zeroCode : Set (I3 → F2)) delta (Fintype.card F2) := by
  intro u
  exact Finset.card_le_univ _

/-- The same full-field budget fails for the projective census. -/
theorem projective_boundary_fails :
    ¬ ProjectiveWorstCaseIncidenceBounded zeroCode delta (Fintype.card F2) := by
  intro h
  let u : WordStack F2 (Fin 2) I3 := ![u0, u1]
  have hu := h u
  have hrows : u 0 = u0 ∧ u 1 = u1 := by simp [u]
  rw [hrows.1, hrows.2, projective_count_eq_three] at hu
  norm_num at hu

/-- **The strict budget hypothesis in `worstCaseIncidenceBounded_iff_projective` is sharp.** -/
theorem worstCaseIncidenceBounded_iff_projective_fails_at_full_field :
    ¬ (WorstCaseIncidenceBounded (F := F2) (A := F2)
          (zeroCode : Set (I3 → F2)) delta (Fintype.card F2) ↔
        ProjectiveWorstCaseIncidenceBounded zeroCode delta (Fintype.card F2)) := by
  intro h
  exact projective_boundary_fails (h.mp affine_boundary_holds)

end ProximityGap.ProjectiveWorstCaseIncidenceBoundary

/-! ## Boundary axiom audit -/
#print axioms ProximityGap.ProjectiveWorstCaseIncidenceBoundary.projective_count_eq_three
#print axioms ProximityGap.ProjectiveWorstCaseIncidenceBoundary.affine_boundary_holds
#print axioms ProximityGap.ProjectiveWorstCaseIncidenceBoundary.projective_boundary_fails
#print axioms
  ProximityGap.ProjectiveWorstCaseIncidenceBoundary.worstCaseIncidenceBounded_iff_projective_fails_at_full_field
