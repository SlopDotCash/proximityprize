/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyThreeRepThree

/-!
# _R353RepThreeCounterexample

Module docstring for `_R353RepThreeCounterexample.lean`.
-/


set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R353RepThreeCounterexample

open ArkLib.ProximityGap.GaussianEnergyThreeRepThree

/-- A zero-sum six-tuple with no antipodal pair is an explicit refutation of `RepThree`.
This is the exact abstract shape of the L1-six web observed at the n=64 bad endpoint. -/
theorem not_repThree_of_zeroSumSix_no_antipode
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {G : Finset F} {c : Fin 6 → F}
    (hc : c ∈ Fintype.piFinset (fun _ : Fin 6 => G))
    (hsum : ∑ i, c i = 0)
    (hno : ∀ i j : Fin 6, i ≠ j → c i ≠ -c j) :
    ¬ RepThree G := by
  intro hrep
  obtain ⟨σ, hσ, hpair⟩ := hrep c hc hsum
  have hne : σ 0 ≠ 0 := hσ.2 0
  have hne' : (0 : Fin 6) ≠ σ 0 := by
    intro h
    exact hne h.symm
  have hneg : -c (σ 0) = c 0 := by
    rw [hpair 0]
    simp
  exact (hno 0 (σ 0) hne') hneg.symm

end ArkLib.ProximityGap.Frontier.R353RepThreeCounterexample

#print axioms
  ArkLib.ProximityGap.Frontier.R353RepThreeCounterexample.not_repThree_of_zeroSumSix_no_antipode
