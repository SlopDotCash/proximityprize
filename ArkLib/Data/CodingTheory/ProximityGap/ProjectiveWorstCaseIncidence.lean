/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
the module exposes the special rebase invariance needed to change away from a bad infinity
slot.  The final consumers feed it directly into the existing operational `mcaDeltaStar` floor
engine.
This does not prove the incidence bound; it removes the affine-chart artifact and identifies
the exact projective object a production proof must bound.  A public theorem for arbitrary
invertible row mixes remains a further API step.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.ProjectiveWorstCaseIncidence

open ProximityGap.MCAProjectiveEquivariance
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

/-- Cardinality of a filtered finite type is invariant under an equivalence. -/
theorem card_filter_comp_equiv {X : Type} [Fintype X] [DecidableEq X]
    (P : X → Prop) [DecidablePred P] (e : X ≃ X) :
    (Finset.univ.filter (fun x => P (e x))).card =
      (Finset.univ.filter P).card := by
  classical
  refine Finset.card_bij' (fun x _ => e x) (fun y _ => e.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro y hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hy).2⟩
  · intro x _hx
    simp
  · intro y _hy
    simp

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
  classical
  unfold badSlotCount
  calc
    (Finset.univ.filter (fun s : Option F =>
        badSlot (F := F) (C : Set (ι → A)) δ u₁ (u₀ + γ • u₁) s)).card =
        (Finset.univ.filter (fun s : Option F =>
          badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ (rebaseSlotEquiv γ s))).card := by
            congr 1
            ext s
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact badSlot_rebase_iff C δ u₀ u₁ γ s
    _ = (Finset.univ.filter (fun s : Option F =>
          badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s)).card :=
      card_filter_comp_equiv
        (fun s : Option F =>
          badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s)
        (rebaseSlotEquiv γ)

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
