/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._Close26_PrimitiveCleanRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._Close27_ImprimitivePlateauExcess

/-!
# Close C27 real-imprimitive parity substrate (#444)

This small compatibility brick restores the committed Lane-B orbit-fold module's missing dependency.
The Lane-B descent file needs only the concrete parity partition of `Fin (2*n)` together with the
already-proven doubling embedding from `_Close26_PrimitiveCleanRecursion`.  We provide that interface
under the namespace it imports, without adding any new open mathematical claim.

What is proven here:
* `dbl` is the existing Close26 doubling map, re-exported in the C27 real-imprimitive namespace.
* `evens n` and `odds n` are the exact parity partition containers of `Fin (2*n)`.
* membership iff lemmas expose the intended predicates `2 ∣ j.val` and `¬ 2 ∣ j.val`.
* `evens_union_odds` and `evens_disjoint_odds` record the partition algebra.

Scope: pure finite parity bookkeeping.  This does **not** prove an odd-fold injectivity, does not close
Lane B, and makes no CORE/BGK/capacity claim.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Close27Real

/-- The C27 namespace uses the same index-doubling embedding as the clean C26 primitive half. -/
abbrev dbl (n : ℕ) : Fin n → Fin (2 * n) := ArkLib.ProximityGap.Close26.dbl n

/-- The even residues of `Fin (2*n)`, i.e. the image side of index doubling. -/
def evens (n : ℕ) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun j => 2 ∣ j.val)

/-- The odd residues of `Fin (2*n)`, the imprimitive complement to the doubled/even part. -/
def odds (n : ℕ) : Finset (Fin (2 * n)) :=
  Finset.univ.filter (fun j => ¬ 2 ∣ j.val)

/-- Membership in `evens n` is exactly evenness of the underlying representative. -/
theorem mem_evens_iff (n : ℕ) (j : Fin (2 * n)) :
    j ∈ evens n ↔ 2 ∣ j.val := by
  simp [evens]

/-- Membership in `odds n` is exactly oddness of the underlying representative. -/
theorem mem_odds_iff (n : ℕ) (j : Fin (2 * n)) :
    j ∈ odds n ↔ ¬ 2 ∣ j.val := by
  simp [odds]

/-- The even and odd residue containers are disjoint. -/
theorem evens_disjoint_odds (n : ℕ) : Disjoint (evens n) (odds n) := by
  rw [Finset.disjoint_left]
  intro j hj_even hj_odd
  rw [mem_evens_iff] at hj_even
  rw [mem_odds_iff] at hj_odd
  exact hj_odd hj_even

/-- The even and odd residue containers cover all of `Fin (2*n)`. -/
theorem evens_union_odds (n : ℕ) : evens n ∪ odds n = (Finset.univ : Finset (Fin (2 * n))) := by
  ext j
  rw [Finset.mem_union, mem_evens_iff, mem_odds_iff]
  simp only [Finset.mem_univ]
  exact iff_true_intro (Classical.em (2 ∣ j.val))

/-- The Close26 image characterization, re-exported in the C27 namespace. -/
theorem dbl_mem_range_iff_even (n : ℕ) (j : Fin (2 * n)) :
    (∃ i : Fin n, dbl n i = j) ↔ 2 ∣ j.val :=
  ArkLib.ProximityGap.Close26.dbl_mem_range_iff_even n j

end ArkLib.ProximityGap.Close27Real

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Close27Real.mem_evens_iff
#print axioms ArkLib.ProximityGap.Close27Real.mem_odds_iff
#print axioms ArkLib.ProximityGap.Close27Real.evens_disjoint_odds
#print axioms ArkLib.ProximityGap.Close27Real.evens_union_odds
#print axioms ArkLib.ProximityGap.Close27Real.dbl_mem_range_iff_even
