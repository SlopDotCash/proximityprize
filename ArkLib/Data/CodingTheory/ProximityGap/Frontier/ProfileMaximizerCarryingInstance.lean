/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MaximizerCarryingReduction

/-!
# A concrete maximizer-carrying consumer instance (Lane A5, Gate 2)

`_MaximizerCarryingReduction.lean` isolates the genuine non-wall route to the delta-star lower pin:
to feed `worstCaseIncidenceBounded_of_someMaximizerReachesFamily` /
`deltaStar_pin_of_maximizersReachFamily`, it suffices to move an actual global maximizer of
`StackBadCount` into a finite family `R` by a count-nondecreasing improvement chain.

This file is a *consumer instance*, written in a NEW file so it does not collide with the socket
file (which is being edited concurrently).  It proves `MaximizersReachFamilyByImprovement` outright
for one concrete profile scheme, and discharges the whole consumer chain down to the delta-star
inequality with NO sorry / NO admit / NO new axiom.

## What is genuinely proven

* `flatProfile_maximizersReachFamily`: a reusable lemma — whenever the bad-scalar profile is
  **flat** (every stack has the same `StackBadCount`), the trivial all-True improvement step is
  count-nondecreasing and carries every maximizer into any nonempty singleton family `{r₀}`.  This
  is the maximizer-carrying hypothesis for a flat profile, proven by a single one-step chain.
* `univCode_*`: the concrete witness.  For the ambient "everything is a codeword" code
  `C = Set.univ`, the MCA `pairJointAgreesOn` clause is always satisfiable, so `mcaEvent` never
  fires and `StackBadCount = 0` for every stack: the profile is flat at height `0`.  We instantiate
  the flat-profile lemma to get `MaximizersReachFamilyByImprovement` on a concrete `n = 8` singleton
  family, then run it through the proven budgeted-max bridge to obtain the delta-star inequality
  `δ ≤ mcaDeltaStar (Set.univ) εstar` for every `δ ≤ 1` and every `εstar`.

## HONESTY / scope (Lane A5 is OFF-WALL, necessary-not-sufficient)

This brick does NOT pin the prize delta-star and does NOT touch the recognized-open BGK/Paley
incidence wall `M(μ_n) ≤ C·√(n log(p/n))`.  Two caveats make that explicit:

* **Degenerate code.**  `C = Set.univ` is the everything-is-a-codeword code; its bad-scalar profile
  is flat at `0`, so the carrying hypothesis is *true but vacuous about hard incidence*.  The hard
  open content is producing a maximizer-carrying chain for an explicit smooth-domain Reed–Solomon
  code at prize scale, where `StackBadCount` is genuinely large.
* **One profile, not all stacks.**  Even taken at face value this is one concrete profile family,
  not the universal sparse-domination theorem.  The flat-profile lemma reduces the carrying
  hypothesis to flatness, which fails for the prize code (that failure is exactly the wall).

So the deliverable is: the maximizer-carrying socket is *consumable* — there is a real, axiom-clean
profile for which `MaximizersReachFamilyByImprovement` holds and drives the proven delta-star
consumer end to end — together with an explicit statement of why this is necessary-not-sufficient.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ArkLib.ProximityGap.Frontier.FloorClosureContract
open ArkLib.ProximityGap.Frontier.MaximizerCarryingReduction

namespace ArkLib.ProximityGap.Frontier.ProfileMaximizerCarryingInstance

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The flat-profile carrying lemma -/

/-- The trivial improvement step: anything improves to anything.  On a flat profile every step is
count-nondecreasing because all counts are equal. -/
def TrivialStep : WordStack A (Fin 2) ι -> WordStack A (Fin 2) ι -> Prop :=
  fun _ _ => True

/-- A profile is *flat* at height `b` when every stack has the same bad-scalar count `b`. -/
def FlatProfileAt (C : Set (ι -> A)) (δ : ℝ≥0) (b : ℕ) : Prop :=
  ∀ u : WordStack A (Fin 2) ι, StackBadCount F C δ u = b

/-- On a flat profile the trivial step is count-nondecreasing. -/
theorem trivialStep_nondecreasing_of_flat
    (C : Set (ι -> A)) (δ : ℝ≥0) {b : ℕ}
    (hflat : FlatProfileAt (F := F) C δ b) :
    StepNondecreasing (F := F) C δ (TrivialStep (ι := ι) (A := A)) := by
  intro u v _hstep
  rw [hflat u, hflat v]

/-- On a flat profile, every stack is a global maximizer. -/
theorem isStackMax_of_flat
    (C : Set (ι -> A)) (δ : ℝ≥0) {b : ℕ}
    (hflat : FlatProfileAt (F := F) C δ b)
    (u : WordStack A (Fin 2) ι) :
    IsStackMax (F := F) C δ u := by
  intro w
  rw [hflat w, hflat u]

/-- **Flat-profile carrying.**  On a flat profile, any nonempty singleton family `{r₀}` carries
every global maximizer through one trivial improvement step.  This is the maximizer-carrying
hypothesis for the flat profile. -/
theorem flatProfile_maximizersReachFamily
    (C : Set (ι -> A)) (δ : ℝ≥0) {b : ℕ}
    (hflat : FlatProfileAt (F := F) C δ b)
    (r₀ : WordStack A (Fin 2) ι) :
    MaximizersReachFamilyByImprovement (F := F) C δ
      (TrivialStep (ι := ι) (A := A)) {r₀} := by
  intro uMax _hmax
  refine ⟨r₀, Finset.mem_singleton_self r₀, ?_⟩
  exact ImprovementChain.tail (ImprovementChain.refl uMax) trivial

/-- A flat profile at height `b` makes any singleton family budgeted at `b`. -/
theorem flatProfile_familyBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {b : ℕ}
    (hflat : FlatProfileAt (F := F) C δ b)
    (r₀ : WordStack A (Fin 2) ι) :
    FamilyBounded F C δ {r₀} b := by
  intro r hr
  rw [Finset.mem_singleton] at hr
  rw [hr, hflat r₀]

/-- **End-to-end flat-profile consumer.**  On a flat profile at height `b`, the proven
maximizer-carrying bridge yields the universal worst-case incidence bound at budget `b`. -/
theorem flatProfile_worstCaseIncidenceBounded
    (C : Set (ι -> A)) (δ : ℝ≥0) {b : ℕ}
    (hflat : FlatProfileAt (F := F) C δ b)
    (r₀ : WordStack A (Fin 2) ι) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := A) C δ b :=
  worstCaseIncidenceBounded_of_maximizersReachFamily C δ
    (trivialStep_nondecreasing_of_flat C δ hflat)
    (flatProfile_maximizersReachFamily C δ hflat r₀)
    (flatProfile_familyBounded C δ hflat r₀)

/-- **Delta-star consumer for a flat profile.**  Drives the proven
`deltaStar_pin_of_maximizersReachFamily` end to end from flatness. -/
theorem flatProfile_deltaStar_pin
    (C : Set (ι -> A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {b : ℕ}
    (hδ : δ ≤ 1)
    (hflat : FlatProfileAt (F := F) C δ b)
    (r₀ : WordStack A (Fin 2) ι)
    (hbudget : (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  deltaStar_pin_of_maximizersReachFamily C εstar hδ
    (trivialStep_nondecreasing_of_flat C δ hflat)
    (flatProfile_maximizersReachFamily C δ hflat r₀)
    (flatProfile_familyBounded C δ hflat r₀)
    hbudget

/-! ## Concrete witness: the ambient universal code is flat at height `0` -/

/-- For the ambient `C = Set.univ`, `pairJointAgreesOn` always holds (pick the two rows themselves),
so the MCA non-agreement clause never fires and `mcaEvent` is always false. -/
theorem mcaEvent_univ_false (δ : ℝ≥0) (u₀ u₁ : ι -> A) (γ : F) :
    ¬ mcaEvent (F := F) (Set.univ : Set (ι -> A)) δ u₀ u₁ γ := by
  rintro ⟨S, _hcard, _hline, hno⟩
  apply hno
  exact ⟨u₀, Set.mem_univ u₀, u₁, Set.mem_univ u₁, fun i _hi => ⟨rfl, rfl⟩⟩

/-- The universal code has `StackBadCount = 0` for every stack: a flat profile at height `0`. -/
theorem univCode_flatProfile (δ : ℝ≥0) :
    FlatProfileAt (F := F) (ι := ι) (A := A) (Set.univ : Set (ι -> A)) δ 0 := by
  intro u
  classical
  unfold StackBadCount
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro γ _hγ
  exact mcaEvent_univ_false δ (u 0) (u 1) γ

/-! ## Concrete `n = 8` instantiation, fully discharged -/

/-- A concrete `n = 8` representative: the zero stack over `ZMod 2`. -/
def r0_n8 : WordStack (ZMod 2) (Fin 2) (Fin 8) := 0

/-- **Concrete consumer instance.**  For the ambient universal code over `ZMod 2` at `n = 8`, the
maximizer-carrying hypothesis holds and drives the delta-star consumer to the inequality
`δ ≤ mcaDeltaStar (Set.univ) εstar` for every `δ ≤ 1` and every `εstar`.  Axiom-clean; no `sorry`. -/
theorem univCode_n8_deltaStar_pin
    (εstar : ℝ≥0∞) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar
          (F := ZMod 2) (A := ZMod 2)
          (Set.univ : Set (Fin 8 -> ZMod 2)) εstar := by
  refine flatProfile_deltaStar_pin
    (F := ZMod 2) (ι := Fin 8) (A := ZMod 2)
    (Set.univ : Set (Fin 8 -> ZMod 2)) εstar hδ
    (univCode_flatProfile δ) r0_n8 ?_
  simp

/-- The concrete `n = 8` maximizer-carrying hypothesis itself, exposed as a standalone fact: every
global `StackBadCount` maximizer reaches the singleton family `{0}` by a count-nondecreasing
improvement chain. -/
theorem univCode_n8_maximizersReachFamily (δ : ℝ≥0) :
    MaximizersReachFamilyByImprovement
      (F := ZMod 2) (ι := Fin 8) (A := ZMod 2)
      (Set.univ : Set (Fin 8 -> ZMod 2)) δ
      (TrivialStep (ι := Fin 8) (A := ZMod 2)) {r0_n8} :=
  flatProfile_maximizersReachFamily
    (F := ZMod 2) (Set.univ : Set (Fin 8 -> ZMod 2)) δ (univCode_flatProfile δ) r0_n8

#print axioms flatProfile_maximizersReachFamily
#print axioms flatProfile_deltaStar_pin
#print axioms univCode_flatProfile
#print axioms univCode_n8_deltaStar_pin
#print axioms univCode_n8_maximizersReachFamily

end ArkLib.ProximityGap.Frontier.ProfileMaximizerCarryingInstance
