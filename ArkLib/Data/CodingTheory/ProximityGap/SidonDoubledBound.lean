/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalGeneral
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalNthRoots
import ArkLib.Data.CodingTheory.ProximityGap.SidonResultantImproved

/-!
# THE DOUBLED (`S = 6`) CASE — `|Res|² ≤ 12^{φ(n)}` (#389)

The improved resultant bound `SidonResultantImproved.abs_resultant_fourTerm_sq_le` (`|Res|² ≤ 8^{φ(n)}`)
covers four-terms with all-distinct exponents (`S = ∑|coeff|² = 4`).  The remaining *genuine*
nontrivial coincidence type for `SidonModNeg` is the **doubled** four-term `2X^i − X^k − X^l`
(`j = i`, `S = 6`).  This file proves its bound `|Res|² ≤ 12^{φ(n)}` via the general Parseval at
`ι = Fin 3`, `s = ![2,−1,−1]` (`∑‖sₐ‖² = 6`), and AM-GM (`φ(n)·12 = 6n`).

Together with the `S = 4` bound, the worst genuine case is `S = 6`, so the **full** improved Sidon
threshold is `p > 12^{φ(n)/2 · 2/n} = 12^{n/4} ≈ 2^{0.896n}` (vs `2^n`).  Axiom-clean.  Issue #389.
-/

open Complex Finset Polynomial
namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **Parseval for the doubled four-term** `2x^i − x^k − x^l` (the `S = 6` case, `j = i`) over the
`n`-th roots: `∑_{x ∈ μ_n} ‖2x^i − x^k − x^l‖² = 6n` for a primitive `n`-th root `ω` whose powers
`ω^i, ω^k, ω^l` are pairwise distinct.  Instantiates `parseval_general` at `ι = Fin 3`,
`s = ![2,−1,−1]` (`∑‖sₐ‖² = 4+1+1 = 6`). -/
theorem parseval_doubled_nthRoots {n : ℕ} (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {i k l : ℕ} (hdist : Function.Injective (![ω ^ i, ω ^ k, ω ^ l] : Fin 3 → ℂ)) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ), ‖2 * x ^ i - x ^ k - x ^ l‖ ^ 2 = n * 6 := by
  have hω1 : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hn
  rw [sum_nthRootsFinset_reindex hω (fun x => ‖2 * x ^ i - x ^ k - x ^ l‖ ^ 2)]
  have heq : ∀ t : ℕ, ‖2 * (ω ^ t) ^ i - (ω ^ t) ^ k - (ω ^ t) ^ l‖ ^ 2
      = ‖∑ a : Fin 3,
          (![2, -1, -1] : Fin 3 → ℂ) a * (![ω ^ i, ω ^ k, ω ^ l] : Fin 3 → ℂ) a ^ t‖ ^ 2 := by
    intro t
    congr 1
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, ← pow_mul, mul_comm i t, mul_comm k t, mul_comm l t]
    ring
  rw [Finset.sum_congr rfl (fun t _ => heq t)]
  have hvn : ∀ a : Fin 3, (![ω ^ i, ω ^ k, ω ^ l] : Fin 3 → ℂ) a ^ n = 1 := by
    intro a; fin_cases a <;> simp <;> rw [pow_right_comm, hω.pow_eq_one, one_pow]
  have hnorm : ∀ a : Fin 3, ‖(![ω ^ i, ω ^ k, ω ^ l] : Fin 3 → ℂ) a‖ = 1 := by
    intro a; fin_cases a <;> simp [norm_pow, hω1]
  rw [parseval_general _ hvn hnorm hdist ![2, -1, -1]]
  congr 1
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  norm_num

/-- **The doubled-four-term resultant bound** (`S = 6` case): for `n = 2^m` and `ω^i, ω^k, ω^l`
pairwise distinct, `|Res(Φ_n, 2X^i − X^k − X^l)|² ≤ 12^{φ(n)}` — i.e. `|Res| ≤ 12^{φ(n)/2}`.  Via
the doubled Parseval `∑ ‖f‖² ≤ 6n` and AM-GM (`φ(n)·12 = 6n`). -/
theorem abs_resultant_doubled_sq_le {m : ℕ} (hm : 1 ≤ m) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (2 ^ m)) {i k l : ℕ}
    (hdist : Function.Injective (![ω ^ i, ω ^ k, ω ^ l] : Fin 3 → ℂ)) :
    (resultant (cyclotomic (2 ^ m) ℤ) (fourTerm i i k l)).natAbs ^ 2 ≤ 12 ^ (2 ^ m).totient := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (fourTerm i i k l) with hR
  set g : ℂ → ℂ := fun ζ => eval ζ ((fourTerm i i k l).map (algebraMap ℤ ℂ)) with hg
  have hgval : ∀ ζ : ℂ, g ζ = 2 * ζ ^ i - ζ ^ k - ζ ^ l := by
    intro ζ
    show eval ζ ((fourTerm i i k l).map (algebraMap ℤ ℂ)) = 2 * ζ ^ i - ζ ^ k - ζ ^ l
    rw [eval_fourTerm_map]; ring
  have hgsq : ∀ ζ : ℂ, Complex.normSq (g ζ) = ‖2 * ζ ^ i - ζ ^ k - ζ ^ l‖ ^ 2 := by
    intro ζ; rw [hgval, Complex.normSq_eq_norm_sq]
  have hcast : (algebraMap ℤ ℂ) R = ((cyclotomic n ℂ).roots.map g).prod :=
    resultant_cast_eq_prod i i k l
  have hprodeq : (Complex.normSq ((algebraMap ℤ ℂ) R))
      = ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) := by
    rw [hcast, map_multiset_prod, Multiset.map_map, cyclotomic.roots_eq_primitiveRoots_val]; rfl
  have hlhs : Complex.normSq ((algebraMap ℤ ℂ) R) = ((R.natAbs : ℝ)) ^ 2 := by
    have hns : ((R.natAbs : ℝ)) ^ 2 = (R : ℝ) ^ 2 := by
      have hcast : (R.natAbs : ℝ) = |(R : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hcast]; exact sq_abs (R : ℝ)
    have halg : (algebraMap ℤ ℂ) R = (R : ℂ) := by simp [algebraMap_int_eq]
    rw [halg, Complex.normSq_intCast, ← pow_two, hns]
  have hsub : primitiveRoots n ℂ ⊆ nthRootsFinset n (1 : ℂ) := by
    intro ζ hζ; rw [mem_primitiveRoots hn0'] at hζ
    rw [mem_nthRootsFinset hn0']; exact hζ.pow_eq_one
  have hsum_le : ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 6 * (n : ℝ) := by
    calc ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ)
        ≤ ∑ ζ ∈ nthRootsFinset n (1 : ℂ), Complex.normSq (g ζ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ζ _ _ => Complex.normSq_nonneg _)
      _ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ‖2 * ζ ^ i - ζ ^ k - ζ ^ l‖ ^ 2 :=
          Finset.sum_congr rfl (fun ζ _ => hgsq ζ)
      _ = n * 6 := parseval_doubled_nthRoots hn0 hω hdist
      _ = 6 * n := by ring
  have hcard : (primitiveRoots n ℂ).card = n.totient := hω.card_primitiveRoots
  have htot : (n.totient : ℝ) * 12 = 6 * n := by
    have h1 : n.totient = 2 ^ (m - 1) := by
      rw [hn_def, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
    have h2 : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [h1, hn_def]; push_cast; rw [h2]; ring
  have hAMGM : ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 12 ^ n.totient := by
    refine prod_le_of_sum_le (primitiveRoots n ℂ) (fun ζ => Complex.normSq (g ζ))
      (fun ζ _ => Complex.normSq_nonneg _) n.totient hcard 12 ?_
    rw [htot]; exact hsum_le
  have hfin : ((R.natAbs : ℝ)) ^ 2 ≤ 12 ^ n.totient := by rw [← hlhs, hprodeq]; exact hAMGM
  have hcastfin : ((R.natAbs ^ 2 : ℕ) : ℝ) ≤ ((12 ^ n.totient : ℕ) : ℝ) := by push_cast; exact hfin
  exact_mod_cast hcastfin

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.parseval_doubled_nthRoots
-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.abs_resultant_doubled_sq_le
