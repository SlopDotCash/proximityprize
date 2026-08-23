/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveProperQuotientBall
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveRankTwoAPI
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GenericQuotientInterpolationSpread
import ArkLib.Data.CodingTheory.HigherOrderMDSOrderTwo

/-!
# Rank-one support intersections and the dual-weight no-go

The proper quotient ball has a precise matroidal interpretation on the production rank-two
stratum.  Every bad normalized slot belongs to a support subspace `B_S`, the pencil is not
contained in `B_S`, and therefore the intersection of the pencil with `B_S` has dimension exactly
one.  This file packages that statement as `badSlot_witnesses_rankOne_supportIntersection`.

Minimum-distance or generalized-Hamming-weight data records the first support size at which such
an intersection can have dimension one or two.  It does not count how many distinct one-dimensional
intersections occur.  The second half makes this obstruction formal: the generic quotient
interpolation spread is an actual Reed--Solomon code whose generator frame is not only MDS but
higher-MDS of order two, yet its MCA numerator is `choose(s,r)`.  Consequently order-two
higher-MDS (and hence ordinary MDS / dual-weight data alone) cannot imply any linear `K * n`
incidence bound whenever `choose(s,r) > K * s * m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap

namespace ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo

open MCAProjectiveEquivariance
open ProjectiveQuotientBall
open ProjectiveQuotientSupport
open ProjectiveRankTwoAPI
open ArkLib.HigherOrderMDS
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread
open ProximityGap.Ownership

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The exact rank-one intersection interface -/

/-- A nonzero point in a proper intersection with a two-dimensional subspace forces that
intersection to have dimension exactly one. -/
theorem finrank_inf_eq_one_of_finrank_eq_two_of_mem_of_not_le
    (C : Submodule F (ι → A)) (P B : Submodule F ((ι → A) ⧸ C))
    (hP : Module.finrank F P = 2) (q : (ι → A) ⧸ C)
    (hq0 : q ≠ 0) (hqP : q ∈ P) (hqB : q ∈ B) (hnot : ¬ P ≤ B) :
    Module.finrank F ↥(P ⊓ B) = 1 := by
  let I : Submodule F ((ι → A) ⧸ C) := P ⊓ B
  have hqI : q ∈ I := ⟨hqP, hqB⟩
  have hIbot : I ≠ ⊥ := by
    intro hbot
    have : q = 0 := by
      have hqbot : q ∈ (⊥ : Submodule F ((ι → A) ⧸ C)) := by
        rw [← hbot]
        exact hqI
      simpa using hqbot
    exact hq0 this
  have hIpos : 1 ≤ Module.finrank F I :=
    Submodule.one_le_finrank_iff.mpr hIbot
  have hIle : Module.finrank F I ≤ 2 := by
    rw [← hP]
    exact Submodule.finrank_mono inf_le_left
  have hIne : Module.finrank F I ≠ 2 := by
    intro hI
    have hIP : I = P :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (hI.trans hP.symm)
    apply hnot
    intro x hx
    have hxI : x ∈ I := by
      rw [hIP]
      exact hx
    change x ∈ P ⊓ B at hxI
    exact hxI.2
  change Module.finrank F I = 1
  omega

/-- A normalized projective point of an independent quotient-row pair is nonzero. -/
theorem quotientSlotPoint_ne_zero_of_rowsIndependent
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A)
    (hind : ProjectiveWorstCaseIncidence.RowsIndependentModCode C u₀ u₁)
    (s : Option F) :
    quotientSlotPoint C u₀ u₁ s ≠ 0 := by
  intro hzero
  apply hind
  refine ⟨(slotCoords s).1, (slotCoords s).2, ?_, ?_⟩
  · rcases s with _ | gamma
    · simp [slotCoords]
    · simp [slotCoords]
  · apply (Submodule.Quotient.mk_eq_zero C).1
    simpa [quotientSlotPoint] using hzero

/-- Every normalized quotient-slot point belongs to its quotient pencil. -/
theorem quotientSlotPoint_mem_quotientPencil
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) (s : Option F) :
    quotientSlotPoint C u₀ u₁ s ∈ quotientPencil C u₀ u₁ := by
  rw [quotientPencil, quotientSlotPoint]
  change C.mkQ ((slotCoords s).1 • u₀ + (slotCoords s).2 • u₁) ∈
    Submodule.span F {C.mkQ u₀, C.mkQ u₁}
  rw [map_add, map_smul, map_smul]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- **Exact matroid interface for a bad rank-two slot.**  Every bad normalized slot of an
independent quotient pencil is witnessed by an admissible support subspace whose intersection
with the pencil has dimension exactly one. -/
theorem badSlot_witnesses_rankOne_supportIntersection
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hind : ProjectiveWorstCaseIncidence.RowsIndependentModCode C u₀ u₁)
    (s : Option F)
    (hbad : badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s) :
    ∃ S : Finset ι,
      WitnessAdmissible δ S ∧
      quotientSlotPoint C u₀ u₁ s ∈ quotientSupportSubmodule C S ∧
      Module.finrank F
        ↥(quotientPencil C u₀ u₁ ⊓ quotientSupportSubmodule C S) = 1 := by
  obtain ⟨S, hS, hmem, hproper⟩ :=
    (mcaEventProj_iff_quotientPencilSupport C δ u₀ u₁
      (slotCoords s).1 (slotCoords s).2).1 hbad
  refine ⟨S, hS, ?_, ?_⟩
  · simpa [quotientSlotPoint] using hmem
  · apply finrank_inf_eq_one_of_finrank_eq_two_of_mem_of_not_le
      (C := C) (P := quotientPencil C u₀ u₁)
      (B := quotientSupportSubmodule C S)
      (q := quotientSlotPoint C u₀ u₁ s)
    · exact finrank_quotientPencil_eq_two C u₀ u₁ hind
    · exact quotientSlotPoint_ne_zero_of_rowsIndependent C u₀ u₁ hind s
    · exact quotientSlotPoint_mem_quotientPencil C u₀ u₁ s
    · simpa [quotientSlotPoint] using hmem
    · exact hproper

/-! ## Order-two higher-MDS cannot supply a linear census bound -/

variable {p s m r K : Nat} [Fact p.Prime] [NeZero s] [NeZero m]

/-- **Parametric dual-weight no-go.**  The quotient interpolation-spread code is an actual
smooth-domain Reed--Solomon code and its generator frame is higher-MDS of order two.  Nevertheless,
if `choose(s,r) > K * (s*m)`, its MCA error at the exact-rate radius is strictly larger than the
putative linear numerator `K * (s*m)` divided by the field size.

Thus ordinary MDS, its dual generalized-Hamming-weight hierarchy, and even order-two higher-MDS
intersection data do not by themselves imply a uniform linear projective-incidence estimate. -/
theorem orderTwoHigherMDS_not_linearMCA_of_choose_gt
    (hs : 1 ≤ s) (hm : 1 ≤ m) (hr2 : 2 ≤ r) (hr : r ≤ s)
    (hk : 2 ≤ (r - 1) * m)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hp : (Nat.choose s r).choose 2 < p)
    (hlarge : K * (s * m) < Nat.choose s r) :
    IsHigherMDS (ZMod p) 2
        (reedSolomonFrame (smoothDom g (s * m) hg) ((r - 1) * m)) ∧
      KKH26.evalCode g (s * m) ((r - 1) * m - 1) =
        ((ProximityGap.SpikeFloor.rsCode
          (smoothDom g (s * m) hg) ((r - 1) * m) :
            Submodule (ZMod p) (Fin (s * m) → ZMod p)) :
              Set (Fin (s * m) → ZMod p)) ∧
      ¬ epsMCA (F := ZMod p)
          (KKH26.evalCode g (s * m) ((r - 1) * m - 1))
          (1 - (r : NNReal) / (s : NNReal)) ≤
        ((K * (s * m) : Nat) : ENNReal) / (p : ENNReal) := by
  have hmds : IsHigherMDS (ZMod p) 2
      (reedSolomonFrame (smoothDom g (s * m) hg) ((r - 1) * m)) :=
    reedSolomonFrame_isHigherMDS_two (smoothDom g (s * m) hg).injective hk
  have hrs := genericQuotient_evalCode_eq_rsCode hm hr2 hg
  have hlower := genericQuotient_epsMCA_lower_bound hs hm hr2 hr hg hp
  have hp0 : (p : ENNReal) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpTop : (p : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hstrict : ((K * (s * m) : Nat) : ENNReal) / (p : ENNReal) <
      ((Nat.choose s r : Nat) : ENNReal) / (p : ENNReal) :=
    ENNReal.div_lt_div_right hp0 hpTop (by exact_mod_cast hlarge)
  refine ⟨hmds, hrs, ?_⟩
  intro hlinear
  exact (not_lt_of_ge hlinear) (hstrict.trans_le hlower)

/-! ## Small explicit witness -/

instance primeFact_ProjectiveDualWeightNoGo_1 : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- The order-eight generator used by the closed `F_4129` smooth-domain pin. -/
theorem orderOf_2386 : orderOf (2386 : ZMod 4129) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ¬ (2386 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
  have h8 : (2386 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
  simpa using orderOf_eq_prime_pow (x := (2386 : ZMod 4129)) h4 h8

/-- **Concrete order-two-higher-MDS counterexample to the coefficient-one linear census.**
The length-eight, dimension-two smooth RS code over `F_4129` is order-two higher-MDS, but at
radius `5/8` its worst MCA numerator is at least `choose(8,3)=56`, hence strictly exceeds `8`. -/
theorem f4129_orderTwoHigherMDS_not_lengthBound :
    IsHigherMDS (ZMod 4129) 2
        (reedSolomonFrame
          (smoothDom (2386 : ZMod 4129) 8 orderOf_2386) 2) ∧
      KKH26.evalCode (2386 : ZMod 4129) 8 1 =
        ((ProximityGap.SpikeFloor.rsCode
          (smoothDom (2386 : ZMod 4129) 8 orderOf_2386) 2 :
            Submodule (ZMod 4129) (Fin 8 → ZMod 4129)) :
              Set (Fin 8 → ZMod 4129)) ∧
      ¬ epsMCA (F := ZMod 4129)
          (KKH26.evalCode (2386 : ZMod 4129) 8 1) (5 / 8) ≤
        (8 : ENNReal) / (4129 : ENNReal) := by
  have h := orderTwoHigherMDS_not_linearMCA_of_choose_gt
    (p := 4129) (s := 8) (m := 1) (r := 3) (K := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    orderOf_2386 (by norm_num [Nat.choose]) (by norm_num [Nat.choose])
  rcases h with ⟨hmds, hrs, hnot⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using hmds
  · simpa using hrs
  · have hradius :
        (1 : NNReal) - ((3 : Nat) : NNReal) / ((8 : Nat) : NNReal) =
          (5 : NNReal) / 8 := by
      refine tsub_eq_of_eq_add ?_
      norm_num
    rw [hradius] at hnot
    simpa using hnot

end ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo.finrank_inf_eq_one_of_finrank_eq_two_of_mem_of_not_le
#print axioms
  ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo.badSlot_witnesses_rankOne_supportIntersection
#print axioms
  ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo.orderTwoHigherMDS_not_linearMCA_of_choose_gt
#print axioms
  ArkLib.ProximityGap.Frontier.ProjectiveDualWeightNoGo.f4129_orderTwoHigherMDS_not_lengthBound
