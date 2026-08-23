/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalBound
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# PARSEVAL OVER THE n-TH ROOTS FINSET — toward the improved Sidon resultant bound (#389)

`SidonParsevalBound.parseval_fourTerm_pow` gives the four-term second moment indexed by `t < n`.
The cyclotomic resultant `Res(Φ_n, f) = ∏_{ζ primitive} f(ζ)` lives over the **`n`-th roots Finset**.
This file bridges the two via a primitive-root reindex, giving the Parseval identity directly over
`nthRootsFinset n 1`:

> **`parseval_fourTerm_nthRoots`** — `∑_{x ∈ μ_n} ‖x^i+x^j−x^k−x^l‖² = 4n` (distinct powers).

Since the primitive roots are a subset of `μ_n`, this bounds `∑_{prim} ‖f(ζ)‖² ≤ 4n`, which through
AM-GM (`SidonParsevalBound.prod_le_of_sum_le`, `φ(2^m)=n/2`) gives `∏_{prim} ‖f(ζ)‖² ≤ 8^{n/2}`, i.e.
`|Res|² ≤ 8^{φ(n)}` (the `2^{3n/4}` improvement).  Issue #389.
-/

open Complex Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- Reindex a sum over `nthRootsFinset n 1` through a primitive root power map. -/
theorem sum_nthRootsFinset_reindex {M : Type*} [AddCommMonoid M] {n : ℕ}
    {ω : ℂ} (hω : IsPrimitiveRoot ω n) (g : ℂ → M) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), g x = ∑ t ∈ Finset.range n, g (ω ^ t) := by
  classical
  have hnod : (Polynomial.nthRoots n (1 : ℂ)).Nodup := hω.nthRoots_one_nodup
  rw [Polynomial.nthRootsFinset_def, Finset.sum, Multiset.toFinset_val, hnod.dedup]
  rw [hω.nthRoots_eq (α := 1) (by simp)]
  simp only [mul_one, Multiset.map_map, Function.comp]
  rfl

/-- **Parseval over the `n`-th roots Finset** (the resultant's domain).  For a primitive `n`-th root
`ω` (`n ≠ 0`) with pairwise-distinct powers `ω^i,…,ω^l`, the four-term `f(x)=x^i+x^j−x^k−x^l`
satisfies `∑_{x ∈ μ_n} ‖f(x)‖² = 4n`. -/
theorem parseval_fourTerm_nthRoots {n : ℕ} (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {i j k l : ℕ} (hdist : Function.Injective (![ω ^ i, ω ^ j, ω ^ k, ω ^ l] : Fin 4 → ℂ)) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), ‖x ^ i + x ^ j - x ^ k - x ^ l‖ ^ 2 = 4 * n := by
  rw [sum_nthRootsFinset_reindex hω (fun x => ‖x ^ i + x ^ j - x ^ k - x ^ l‖ ^ 2)]
  have hrw : ∀ t ∈ Finset.range n,
      ‖(ω ^ t) ^ i + (ω ^ t) ^ j - (ω ^ t) ^ k - (ω ^ t) ^ l‖ ^ 2
        = ‖ω ^ (i * t) + ω ^ (j * t) - ω ^ (k * t) - ω ^ (l * t)‖ ^ 2 := by
    intro t _; rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i t, mul_comm j t,
      mul_comm k t, mul_comm l t]
  rw [Finset.sum_congr rfl hrw]
  exact parseval_fourTerm_pow hn hω hdist

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.parseval_fourTerm_nthRoots
