/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalNthRoots
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftClosed
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# THE IMPROVED CYCLOTOMIC RESULTANT BOUND — `|Res|² ≤ 8^{φ(n)}` (#389)

The committed `CyclotomicResultantBound.abs_resultant_le` gives `|Res(Φ_n, f)| ≤ 4^{φ(n)} = 2^n`
via the **pointwise** estimate `‖f(ζ)‖ ≤ 4`.  This file proves the **sharp** bound
`|Res|² ≤ 8^{φ(n)}` (i.e. `|Res| ≤ 8^{φ(n)/2} = 2^{3n/4}`, since `8^{n/2} = 2^{3n/2}`) for `n = 2^m`
and pairwise-distinct exponents, replacing the pointwise estimate by the **Parseval `ℓ²` average**
`∑_{ζ ∈ μ_n} ‖f(ζ)‖² = 4n` (`parseval_fourTerm_nthRoots`) and **AM-GM** over the `φ(n) = n/2`
primitive roots (`prod_le_of_sum_le`).  Probe-verified tight (`max |Res| = 2^{3n/4}`).

This sharpens the small-subgroup Sidon threshold from `p > 2^n` to `p > 2^{3n/4}` — a `33%` larger
unconditional Sidon regime `n < (4/3) log₂ p`.  Axiom-clean.  Issue #389.
-/

open Complex Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **THE IMPROVED RESULTANT BOUND.**  For `n = 2^m` (`m ≥ 1`) and a four-term whose `ω`-powers are
pairwise distinct, the cyclotomic resultant satisfies `|Res(Φ_n, f)|² ≤ 8^{φ(n)}` — i.e.
`|Res| ≤ 8^{φ(n)/2} = 2^{3n/4}`, improving the pointwise bound `|Res| ≤ 4^{φ(n)} = 2^n`.  Via
Parseval `∑_{prim} ‖f(ζ)‖² ≤ 4n` and AM-GM over the `φ(n) = n/2` primitive roots. -/
theorem abs_resultant_fourTerm_sq_le {m : ℕ} (hm : 1 ≤ m) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (2 ^ m)) {i j k l : ℕ}
    (hdist : Function.Injective (![ω ^ i, ω ^ j, ω ^ k, ω ^ l] : Fin 4 → ℂ)) :
    (resultant (cyclotomic (2 ^ m) ℤ) (fourTerm i j k l)).natAbs ^ 2 ≤ 8 ^ (2 ^ m).totient := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (fourTerm i j k l) with hR
  set g : ℂ → ℂ := fun ζ => eval ζ ((fourTerm i j k l).map (algebraMap ℤ ℂ)) with hg
  have hgval : ∀ ζ : ℂ, g ζ = ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l := fun ζ => eval_fourTerm_map _ _ i j k l
  have hgsq : ∀ ζ : ℂ, Complex.normSq (g ζ) = ‖ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l‖ ^ 2 := by
    intro ζ; rw [hgval, Complex.normSq_eq_norm_sq]
  have hcast : (algebraMap ℤ ℂ) R = ((cyclotomic n ℂ).roots.map g).prod :=
    resultant_cast_eq_prod i j k l
  have hprodeq : (Complex.normSq ((algebraMap ℤ ℂ) R))
      = ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) := by
    rw [hcast, map_multiset_prod, Multiset.map_map,
      cyclotomic.roots_eq_primitiveRoots_val]
    rfl
  -- LHS = (R.natAbs)²
  have hlhs : Complex.normSq ((algebraMap ℤ ℂ) R) = ((R.natAbs : ℝ)) ^ 2 := by
    have hns : ((R.natAbs : ℝ)) ^ 2 = (R : ℝ) ^ 2 := by
      have hcast : (R.natAbs : ℝ) = |(R : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hcast]; exact sq_abs (R : ℝ)
    have halg : (algebraMap ℤ ℂ) R = (R : ℂ) := by simp [algebraMap_int_eq]
    rw [halg, Complex.normSq_intCast, ← pow_two, hns]
  -- the sum over primitive roots is ≤ 4n
  have hsub : primitiveRoots n ℂ ⊆ nthRootsFinset n (1 : ℂ) := by
    intro ζ hζ
    rw [mem_primitiveRoots hn0'] at hζ
    rw [mem_nthRootsFinset hn0']; exact hζ.pow_eq_one
  have hsum_le : ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 4 * (n : ℝ) := by
    calc ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ)
        ≤ ∑ ζ ∈ nthRootsFinset n (1 : ℂ), Complex.normSq (g ζ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ζ _ _ => Complex.normSq_nonneg _)
      _ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ‖ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l‖ ^ 2 :=
          Finset.sum_congr rfl (fun ζ _ => hgsq ζ)
      _ = 4 * n := parseval_fourTerm_nthRoots hn0 hω hdist
  have hcard : (primitiveRoots n ℂ).card = n.totient := hω.card_primitiveRoots
  have htot : (n.totient : ℝ) * 8 = 4 * n := by
    have h1 : n.totient = 2 ^ (m - 1) := by
      rw [hn_def, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
    rw [h1, hn_def]; push_cast
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1; omega
  have hAMGM : ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 8 ^ n.totient := by
    refine prod_le_of_sum_le (primitiveRoots n ℂ) (fun ζ => Complex.normSq (g ζ))
      (fun ζ _ => Complex.normSq_nonneg _) n.totient hcard 8 ?_
    rw [htot]; exact hsum_le
  have hfin : ((R.natAbs : ℝ)) ^ 2 ≤ 8 ^ n.totient := by
    rw [← hlhs, hprodeq]; exact hAMGM
  have hcastfin : ((R.natAbs ^ 2 : ℕ) : ℝ) ≤ ((8 ^ n.totient : ℕ) : ℝ) := by push_cast; exact hfin
  exact_mod_cast hcastfin

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.abs_resultant_fourTerm_sq_le
