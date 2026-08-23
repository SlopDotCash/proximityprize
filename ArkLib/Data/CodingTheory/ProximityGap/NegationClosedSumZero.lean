/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound

/-!
# The antipodal-pairing converse: paired ⟹ zero-sum (#389, a Bessel-law brick)

The Bessel even-moment law `E_r(μ_n) = (2r)!·[x^r] I₀(2√x)^{n/2}` (see `scripts/conjectures/`)
rests on the equivalence *zero-sum ⟺ negation-balanced*. The forward direction is the deep
antipodal-closure (`ACL`, a char-0 / above-threshold theorem). **This file lands the converse
direction, unconditionally**: if a `2r`-tuple `c` is antipodally paired by a pairing `σ`
(`c (σ i) = − c i`), then `∑ i, c i = 0`.

* `antipodalConsistent_sum_zero` — paired ⟹ zero-sum, by the transversal split
  `∑ univ = ∑ over lowerHalf of (c i + c (σ i))` and pointwise cancellation `c i + (−c i) = 0`.
  No characteristic hypothesis (the cancellation is per-pair, not `2 • s = 0`).

Together with `zeroSumCount_le_pairings` (the K1 counting bound) this pins the structure that
makes the negation-balanced count — hence the Bessel coefficient — the exact moment under `ACL`.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
* `NegationClosedWalkBound.lean` (`IsPairing`, `lowerHalf`); `scripts/conjectures/PROOFS.md`
  (Theorem 1, step 2 converse); issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.NegationClosedWalk

variable {F : Type*} [Field F]

/-- **The antipodal-pairing converse (unconditional).** If `σ` is a pairing of `Fin (2r)` and
`c (σ i) = − c i` for every `i`, then `∑ i, c i = 0`: the transversal `lowerHalf σ` splits the
sum into matched pairs `c i + c (σ i) = c i + (− c i) = 0`. -/
theorem antipodalConsistent_sum_zero {r : ℕ} {σ : Equiv.Perm (Fin (2 * r))}
    (hσ : IsPairing σ) {c : Fin (2 * r) → F} (hc : ∀ i, c (σ i) = - c i) :
    ∑ i, c i = 0 := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hfix : ∀ i, σ i ≠ i := hσ.2
  -- split the full sum at the transversal predicate `i < σ i`
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i < σ i) c]
  -- the complement (`¬ i < σ i`) reindexes onto the transversal via `σ`
  have hcompl : (∑ i ∈ Finset.univ.filter (fun i => ¬ i < σ i), c i)
      = ∑ i ∈ Finset.univ.filter (fun i => i < σ i), c (σ i) := by
    refine Finset.sum_nbij' (fun i => σ i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
    · -- maps complement → transversal
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hne : σ i ≠ i := hfix i
      have : σ i < i := lt_of_le_of_ne (not_lt.mp hi) (by simpa using hne)
      simpa [hinv i] using this
    · -- maps transversal → complement
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hinv i]
      exact not_lt.mpr (le_of_lt hi)
    · intro i _; exact hinv i
    · intro i _; exact hinv i
    · intro i _; show c i = c (σ (σ i)); rw [hinv i]
  rw [hcompl, ← Finset.sum_add_distrib]
  -- each matched pair cancels: c i + c (σ i) = c i + (− c i) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [hc i]; ring

/-! ## Source audit -/

#print axioms antipodalConsistent_sum_zero

end ArkLib.ProximityGap.NegationClosedWalk
