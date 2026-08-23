/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R62SplitSavingLever

/-!
# LANE B2 (#466 round 63): monotonicity for the split sextic inputs

Round 62 names the exact common-constant cancellation input left by the split route.  This file
adds the local monotonicity and constant-unification lemmas for the two split hypotheses
themselves.  These are the adapters needed by any later Katz/Deligne or cube-lag proof that
lands the generic and cube estimates with different explicit constants before passing to one
absolute cancellation constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity

open ArkLib.ProximityGap.Frontier.R41SexticInputSplit
open ArkLib.ProximityGap.Frontier.R42CubeLagInput
open ArkLib.ProximityGap.Frontier.R62SplitSavingLever

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- The generic non-cube sextic input is monotone in its cancellation constant. -/
theorem genericSexticVarietyInput_mono
    {C C' : ℝ}
    (hC : C ≤ C')
    (hgeneric : GenericSexticVarietyInput χ lam G C) :
    GenericSexticVarietyInput χ lam G C' := by
  intro u hu a b a' b' t ht hshape
  have hbase := hgeneric u hu a b a' b' t ht hshape
  have hscale_nonneg :
      0 ≤ Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by positivity
  have hbudget :
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
        ≤ C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    calc
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
          = C * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring
      _ ≤ C' * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hC hscale_nonneg
      _ = C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring
  exact hbase.trans hbudget

/-- The concrete cube-lag input is monotone in its cancellation constant. -/
theorem cubeLagInput_mono
    {C C' : ℝ}
    (hC : C ≤ C')
    (hcube : CubeLagInput χ lam G C) :
    CubeLagInput χ lam G C' := by
  intro u hu t ht
  have hbase := hcube u hu t ht
  have hscale_nonneg :
      0 ≤ Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by positivity
  have hbudget :
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
        ≤ C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by
    calc
      C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2
          = C * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) := by ring
      _ ≤ C' * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hC hscale_nonneg
      _ = C' * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring
  exact hbase.trans hbudget

/-- Split cancellation is monotone in its common constant. -/
theorem splitSexticCancellationInput_mono
    {C C' : ℝ}
    (hC : C ≤ C')
    (hsplit : SplitSexticCancellationInput χ lam G C) :
    SplitSexticCancellationInput χ lam G C' :=
  ⟨genericSexticVarietyInput_mono hC hsplit.1, cubeLagInput_mono hC hsplit.2⟩

/-- Generic and cube estimates with separate constants unify into the common-constant split
cancellation input at any larger `C`. -/
theorem splitSexticCancellationInput_of_generic_cubeLag_le
    {Cgeneric Ccube C : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube)
    (hCg : Cgeneric ≤ C) (hCc : Ccube ≤ C) :
    SplitSexticCancellationInput χ lam G C :=
  ⟨genericSexticVarietyInput_mono hCg hgeneric, cubeLagInput_mono hCc hcube⟩

/-- Generic and cube estimates unify at the maximum of their two constants. -/
theorem splitSexticCancellationInput_of_generic_cubeLag_max
    {Cgeneric Ccube : ℝ}
    (hgeneric : GenericSexticVarietyInput χ lam G Cgeneric)
    (hcube : CubeLagInput χ lam G Ccube) :
    SplitSexticCancellationInput χ lam G (max Cgeneric Ccube) :=
  splitSexticCancellationInput_of_generic_cubeLag_le hgeneric hcube
    (le_max_left _ _) (le_max_right _ _)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity.genericSexticVarietyInput_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity.cubeLagInput_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity.splitSexticCancellationInput_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity.splitSexticCancellationInput_of_generic_cubeLag_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity.splitSexticCancellationInput_of_generic_cubeLag_max

end ArkLib.ProximityGap.Frontier.R63SplitInputMonotonicity
