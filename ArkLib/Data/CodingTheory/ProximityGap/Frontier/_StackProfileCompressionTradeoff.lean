/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

/-!
# Cardinality tradeoff for stack profiles

The profile-fiber-max interface says a useful classification proof must choose a profile map whose
fibers have analyzable maximizers.  This file records the basic counting pressure on such a profile.

For a finite profile type `P`, the stack universe is covered by the profile fibers.  If every fiber
has size at most `K`, then

`#WordStack A (Fin 2) ι <= #P * K`.

Equivalently, any profile compression with `#P * K` below the stack-universe size must have at least
one fiber larger than `K`.  Thus a small binder/adjacent-pattern/floor profile does not avoid the
large-fiber problem; it concentrates the hard maximizer theorem inside large fibers.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {A : Type} [Fintype A] [DecidableEq A]

/-- The two-row stack universe has size `|A|^(2*|ι|)`. -/
theorem card_wordStack_fin2_eq :
    Fintype.card (WordStack A (Fin 2) ι) = (Fintype.card A) ^ (2 * Fintype.card ι) := by
  show Fintype.card (Fin 2 -> ι -> A) = (Fintype.card A) ^ (2 * Fintype.card ι)
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul]
  rw [Nat.mul_comm]

/-- The finite fiber of stacks with profile `p`. -/
noncomputable def profileFiber {P : Type} [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) (p : P) :
    Finset (WordStack A (Fin 2) ι) := by
  classical
  exact Finset.univ.filter (fun u => profile u = p)

@[simp] theorem mem_profileFiber {P : Type} [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P} {p : P}
    {u : WordStack A (Fin 2) ι} :
    u ∈ profileFiber profile p ↔ profile u = p := by
  classical
  simp [profileFiber]

/-- The stack universe is covered by the fibers of any finite profile map. -/
theorem stackUniverse_subset_profileFibers {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) :
    (Finset.univ : Finset (WordStack A (Fin 2) ι)) ⊆
      (Finset.univ : Finset P).biUnion (fun p => profileFiber profile p) := by
  intro u _hu
  exact Finset.mem_biUnion.mpr
    ⟨profile u, Finset.mem_univ _, by simp [profileFiber]⟩

/-- If every profile fiber has size at most `K`, then the stack universe has size at most
`#P * K`. -/
theorem stackUniverse_card_le_profileCard_mul_fiberCap
    {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) {K : ℕ}
    (hcap : ∀ p : P, (profileFiber profile p).card ≤ K) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ Fintype.card P * K := by
  classical
  calc
    Fintype.card (WordStack A (Fin 2) ι)
        = (Finset.univ : Finset (WordStack A (Fin 2) ι)).card := by
          simp
    _ ≤ ((Finset.univ : Finset P).biUnion (fun p => profileFiber profile p)).card :=
        Finset.card_le_card (stackUniverse_subset_profileFibers (A := A) profile)
    _ ≤ (Finset.univ : Finset P).card * K :=
        Finset.card_biUnion_le_card_mul
          (Finset.univ : Finset P) (fun p => profileFiber profile p) K
          (fun p _hp => hcap p)
    _ = Fintype.card P * K := by simp

/-- If `#P * K` is smaller than the stack universe, some profile fiber has size larger than `K`. -/
theorem exists_large_profileFiber_of_profileCard_mul_lt_stackUniverse
    {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) {K : ℕ}
    (hsmall : Fintype.card P * K < Fintype.card (WordStack A (Fin 2) ι)) :
    ∃ p : P, K < (profileFiber profile p).card := by
  by_contra hno
  have hcap : ∀ p : P, (profileFiber profile p).card ≤ K := by
    intro p
    exact Nat.le_of_not_gt (fun hgt => hno ⟨p, hgt⟩)
  exact (not_lt_of_ge
    (stackUniverse_card_le_profileCard_mul_fiberCap
      (A := A) (profile := profile) (K := K) hcap)) hsmall

/-- A singleton profile type can classify all stacks only by putting the whole stack universe in one
fiber. -/
theorem singletonProfile_stackUniverse_card_le_fiber
    {P : Type} [Fintype P] [DecidableEq P] [Unique P]
    (profile : WordStack A (Fin 2) ι -> P) :
    Fintype.card (WordStack A (Fin 2) ι)
      ≤ (profileFiber profile default).card := by
  classical
  have hcap : ∀ p : P, (profileFiber profile p).card ≤ (profileFiber profile default).card := by
    intro p
    have hp : p = default := Subsingleton.elim p default
    rw [hp]
  simpa using
    (stackUniverse_card_le_profileCard_mul_fiberCap
      (A := A) (profile := profile) (K := (profileFiber profile default).card) hcap)

/-- Explicit exponential form: if all profile fibers have size at most `K`, then
`|A|^(2|ι|) <= #P*K`. -/
theorem cardA_pow_le_profileCard_mul_fiberCap
    {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) {K : ℕ}
    (hcap : ∀ p : P, (profileFiber profile p).card ≤ K) :
    (Fintype.card A) ^ (2 * Fintype.card ι) ≤ Fintype.card P * K := by
  rw [← card_wordStack_fin2_eq (A := A) (ι := ι)]
  exact stackUniverse_card_le_profileCard_mul_fiberCap
    (A := A) (profile := profile) (K := K) hcap

/-- Explicit exponential obstruction: if `#P*K < |A|^(2|ι|)`, then some fiber is larger than `K`. -/
theorem exists_large_profileFiber_of_profileCard_mul_lt_exp
    {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P) {K : ℕ}
    (hsmall : Fintype.card P * K < (Fintype.card A) ^ (2 * Fintype.card ι)) :
    ∃ p : P, K < (profileFiber profile p).card := by
  rw [← card_wordStack_fin2_eq (A := A) (ι := ι)] at hsmall
  exact exists_large_profileFiber_of_profileCard_mul_lt_stackUniverse
    (A := A) (profile := profile) (K := K) hsmall

/-- An injective profile has fibers of size at most one. -/
theorem profileFiber_card_le_one_of_injective
    {P : Type} [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P}
    (hinj : Function.Injective profile) (p : P) :
    (profileFiber profile p).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  apply hinj
  rw [mem_profileFiber.mp hx, mem_profileFiber.mp hy]

/-- An injective profile space must be at least as large as the full stack universe.  Thus a small
profile can only compress by aggregating many stacks into nontrivial fibers. -/
theorem stackUniverse_card_le_profileCard_of_injective
    {P : Type} [Fintype P] [DecidableEq P]
    {profile : WordStack A (Fin 2) ι -> P}
    (hinj : Function.Injective profile) :
    Fintype.card (WordStack A (Fin 2) ι) ≤ Fintype.card P := by
  simpa using
    (stackUniverse_card_le_profileCard_mul_fiberCap
      (A := A) (ι := ι) (profile := profile) (K := 1)
      (profileFiber_card_le_one_of_injective (A := A) (ι := ι) hinj))

/-- If the profile space is smaller than the stack universe, the profile map cannot be injective. -/
theorem not_injective_profile_of_profileCard_lt_stackUniverse
    {P : Type} [Fintype P] [DecidableEq P]
    (profile : WordStack A (Fin 2) ι -> P)
    (hsmall : Fintype.card P < Fintype.card (WordStack A (Fin 2) ι)) :
    ¬ Function.Injective profile := by
  intro hinj
  exact (not_lt_of_ge (stackUniverse_card_le_profileCard_of_injective
    (A := A) (ι := ι) (profile := profile) hinj)) hsmall

end ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.card_wordStack_fin2_eq
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.stackUniverse_subset_profileFibers
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.stackUniverse_card_le_profileCard_mul_fiberCap
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.exists_large_profileFiber_of_profileCard_mul_lt_stackUniverse
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.singletonProfile_stackUniverse_card_le_fiber
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.cardA_pow_le_profileCard_mul_fiberCap
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.exists_large_profileFiber_of_profileCard_mul_lt_exp
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.profileFiber_card_le_one_of_injective
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.stackUniverse_card_le_profileCard_of_injective
#print axioms ArkLib.ProximityGap.Frontier.StackProfileCompressionTradeoff.not_injective_profile_of_profileCard_lt_stackUniverse
