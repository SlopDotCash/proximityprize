/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.AgreementQuadratic

/-! # A quadratic list-size bound one step beyond strict Johnson at rate one eighth -/

namespace ProximityGap.InterleavedListJohnsonQuadratic

open Code InterleavedListJohnsonRank AgreementQuadratic

/-- At rate one eighth the degree-two set bound certifies the first integer
agreement count below strict Johnson, over any field and for any interleaving. -/
theorem eighth_below_johnson {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity : ℕ) :
    AtErrors D arity 134217728 694116763 1931589824 := by
  classical
  apply interleaved_lambda_le_of_block_bound D 134217728 379625061 arity 1931589824 _
    (by norm_num)
  intro m S hw hp
  have h := constant_weight_bound (Finset.univ : Finset (Fin m)) S 379625061 134217727
    (fun i _ => hw i) (fun i _ j _ hij => hp hij) (by decide) (by norm_num)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, variance, overlap] at h
  norm_num at h
  by_contra! hbad
  have hm : (1931589825 : ℝ) ≤ m := by exact_mod_cast hbad
  linarith

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The improved rate-one-eighth endpoint is inside the second nominated
prime's exact security budget. -/
theorem second_prime_eighth_below_johnson
    (D : Fin 1073741824 ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (arity : ℕ) :
    AtErrors D arity 134217728 694116763 (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2^128) :=
  (eighth_below_johnson D arity).trans
    (by exact_mod_cast
      (show 1931589824 ≤ ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2^128 by decide))

end ProximityGap.InterleavedListJohnsonQuadratic

#print axioms ProximityGap.InterleavedListJohnsonQuadratic.eighth_below_johnson
#print axioms ProximityGap.InterleavedListJohnsonQuadratic.second_prime_eighth_below_johnson
