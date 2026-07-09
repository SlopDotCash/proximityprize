/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R355GeneratorWebWickConsumer

/-!
# R362: the prime-ideal L1 shell is the exact R355 producer

R361's finite census naturally lives in the full integer evaluation kernel, whereas R355 is
stated for realized collision relations.  This file identifies the precise bridge: every
depth-`s` realized relation lies in the evaluation-kernel shell of radius `2(r-s)`.  Therefore
the square-root shell census

```text
k! * #kerShell(2k) <= 3^k * m^k
```

implies R355's `GeneratorWebCensus`, and hence its `8^r`-times-Wick collision bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R362KernelShellWickWeld

open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R324KernelRelationLengthStratification
open ArkLib.ProximityGap.Frontier.R326DominantRecurrenceL1Contraction
open ArkLib.ProximityGap.Frontier.R355GeneratorWebWickConsumer

/-- Integer vectors of exact `L1` mass `L` in the kernel of evaluation at `g`. -/
noncomputable def kernelL1Shell
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m L : ℕ) : Finset (Fin m → ℤ) :=
  (l1Sphere m L).filter (fun d => evalVec g m d = 0)

theorem mem_l1Sphere_of_natL1_eq {m L : ℕ} {d : Fin m → ℤ}
    (hd : natL1 d = L) : d ∈ l1Sphere m L := by
  classical
  rw [l1Sphere, Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.mpr (fun j => ?_), hd⟩
  rw [Finset.mem_Icc]
  have hj : (d j).natAbs ≤ L := by
    rw [← hd]
    unfold natL1
    exact Finset.single_le_sum
      (f := fun i : Fin m => (d i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hjcast : ((d j).natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hj
  have hj' : |d j| ≤ (L : ℤ) := by simpa using hjcast
  exact abs_le.mp hj'

/-- A realized depth-`s` relation belongs to the full kernel shell of radius `2(r-s)`. -/
theorem relationCancellationStratum_subset_kernelL1Shell
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) :
    relationCancellationStratum g m r s ⊆ kernelL1Shell g m (2 * (r - s)) := by
  classical
  intro d hd
  rw [kernelL1Shell, Finset.mem_filter]
  have hdrel : d ∈ shadowKernelRelations g (2 * m) m r :=
    (Finset.mem_filter.mp hd).1
  have heval := (shadowKernelRelation_ne_zero_and_evalVec_eq_zero g (2 * m) m r hdrel).2
  refine ⟨mem_l1Sphere_of_natL1_eq ?_, heval⟩
  have hdepth := decomposition_of_mem_relationCancellationStratum g m r s hd
  unfold natL1
  omega

/-- Consequently the realized stratum cardinality is bounded by the full shell cardinality. -/
theorem card_relationCancellationStratum_le_kernelL1Shell
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) :
    (relationCancellationStratum g m r s).card ≤
      (kernelL1Shell g m (2 * (r - s))).card :=
  Finset.card_le_card (relationCancellationStratum_subset_kernelL1Shell g m r s)

/-- The normalized full-shell target suggested by R361. -/
def KernelShellCensus
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) : Prop :=
  ∀ k ≤ r,
    k.factorial * (kernelL1Shell g m (2 * k)).card ≤ 3 ^ k * m ^ k

/-- A full evaluation-kernel shell census implies the realized generator-web census. -/
theorem generatorWebCensus_of_kernelShellCensus
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hshell : KernelShellCensus g m r) :
    GeneratorWebCensus g m r := by
  intro s hs
  have hsr : s ≤ r := Nat.le_of_lt (Finset.mem_range.mp hs)
  calc
    (r - s).factorial * (relationCancellationStratum g m r s).card ≤
        (r - s).factorial * (kernelL1Shell g m (2 * (r - s))).card :=
      Nat.mul_le_mul_left _ (card_relationCancellationStratum_le_kernelL1Shell g m r s)
    _ ≤ 3 ^ (r - s) * m ^ (r - s) := hshell (r - s) (Nat.sub_le r s)

/-- **Prime-ideal shell to Wick.** This is the complete R361 -> R355 implication. -/
theorem factorial_mul_shadowCollisionMass_le_of_kernelShellCensus
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hshell : KernelShellCensus g m r) :
    r.factorial * shadowCollisionMass g (2 * m) m r ≤
      4 ^ r * (r + r).factorial * m ^ r :=
  factorial_mul_shadowCollisionMass_le_of_generatorWebCensus g m r
    (generatorWebCensus_of_kernelShellCensus g m r hshell)

end ArkLib.ProximityGap.Frontier.R362KernelShellWickWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R362KernelShellWickWeld.relationCancellationStratum_subset_kernelL1Shell
#print axioms
  ArkLib.ProximityGap.Frontier.R362KernelShellWickWeld.generatorWebCensus_of_kernelShellCensus
#print axioms
  ArkLib.ProximityGap.Frontier.R362KernelShellWickWeld.factorial_mul_shadowCollisionMass_le_of_kernelShellCensus
