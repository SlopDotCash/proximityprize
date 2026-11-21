/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# One deletion beyond the strict Johnson region

Restricting to the blocks which omit a coordinate makes the underlying
universe smaller while preserving the block size and intersection cap.
Double counting excluded coordinates gives the stated list bound.
-/

namespace ProximityGap.InterleavedListJohnsonPuncture

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
  (card_le_universe_of_equal_card_pair_inter_le)

open Code InterleavedListJohnsonRank

/-- Count the excluded block-point incidences after applying the strict
obtuse-set bound on each punctured universe of size `n-1`. -/
theorem punctured_block_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {m t s : ℕ} (S : Fin m → Finset ι) (ht : 1 ≤ t)
    (hsize : ∀ i, (S i).card = t) (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ s)
    (hstrict : (Fintype.card ι - 1) * s < t ^ 2) :
    m * (Fintype.card ι - t) ≤ Fintype.card ι * (Fintype.card ι - 1) := by
  classical
  have fiber (x : ι) : (Finset.univ.filter fun i => x ∉ S i).card ≤ Fintype.card ι - 1 := by
    let T := Finset.univ.filter fun i => x ∉ S i
    let A (i : ↥T) := (S i.val).subtype (fun a => a ≠ x)
    have hA (i : ↥T) : (A i).card = t := by
      have hx : x ∉ S i.val := (Finset.mem_filter.mp i.property).2
      have he : ((S i.val).filter fun a => a ≠ x) = S i.val := by
        apply Finset.filter_eq_self.mpr
        rintro y hy rfl
        exact hx hy
      rw [show (A i).card = ((S i.val).filter fun a => a ≠ x).card from Finset.card_subtype _ _, he]
      exact hsize i.val
    have hp : Pairwise fun i j => (A i ∩ A j).card ≤ s := by
      intro i j hne
      have he : A i ∩ A j = (S i.val ∩ S j.val).subtype (fun a => a ≠ x) := by
        ext a
        simp [A]
      rw [he, Finset.card_subtype]
      exact (Finset.card_filter_le _ _).trans (hpair (fun h => hne (Subtype.ext h)))
    have h := card_le_universe_of_equal_card_pair_inter_le
      A (Fintype.card ι - 1) t s (Set.card_ne_eq x) ht hA hp (by omega)
    change T.card ≤ _
    simpa only [Fintype.card_coe] using h
  have hlo (i : Fin m) : (Finset.univ.bipartiteAbove (fun j x => x ∉ S j) i).card =
      Fintype.card ι - t := by
    have he : Finset.univ.bipartiteAbove (fun j x => x ∉ S j) i = (S i)ᶜ := by ext; simp
    rw [he, Finset.card_compl, hsize]
  have h := Finset.card_mul_le_card_mul (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset ι)) (fun i x => x ∉ S i) (fun i _ => (hlo i).ge)
    (fun x _ => fiber x)
  simpa using h

/-- One step beyond strict Johnson at rate one eighth, the punctured
bound permits at most 1,660,990,722 interleaved codewords at each center. -/
theorem eighth_below_johnson {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity : ℕ) :
    AtErrors D arity 134217728 694116763 1660990722 := by
  classical
  apply interleaved_lambda_le_of_block_bound D 134217728 379625061 arity 1660990722 _
    (by norm_num)
  intro m S hw hp
  have h := punctured_block_bound S (by decide : 1 ≤ 379625061) hw hp (by norm_num)
  simp only [Fintype.card_fin] at h
  omega

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The second named prime meets its security budget at the improved radius. -/
theorem second_prime_eighth_below_johnson
    (D : Fin 1073741824 ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (arity : ℕ) :
    AtErrors D arity 134217728 694116763 (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2^128) :=
  (eighth_below_johnson D arity).trans
    (by exact_mod_cast
      (show 1660990722 ≤ ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2^128 by decide))

end ProximityGap.InterleavedListJohnsonPuncture

#print axioms ProximityGap.InterleavedListJohnsonPuncture.punctured_block_bound
#print axioms ProximityGap.InterleavedListJohnsonPuncture.second_prime_eighth_below_johnson
