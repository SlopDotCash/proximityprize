/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungUnconditionalGeneral

/-!
# The halo-free threshold: above an explicit prime bound, finite-field solutions are
# exactly the antipodal-closed subsets

O145/O149 measured the per-prime halo of the census systems (one rotation orbit per prime,
each member "monogamous" to the primes dividing its constraint norms). This file proves the
**halo-free threshold** at depth 1, discharging the named halo surface above an explicit
bound: for a prime `p` with `(2^{m−1})^{2^{m−1}} < p` and a primitive `2^m`-th root
`g ∈ F_p`,

  a subset `E ⊆ [0, 2^m)` has `∑_{e∈E} g^e = 0` **iff** `E` is antipodal-closed
  (`j ∈ E ↔ j + 2^{m−1} ∈ E`).

The forward implication ("solutions are antipodal-closed") is the finite-field counterpart
of the char-0 subset Lam–Leung theorem (`subset_neg_mem_of_sum_zero`); the key device makes
it *unconditional above the threshold with no characteristic-zero input*: reducing the
exponent-sum polynomial mod `Φ_{2^m} = X^{2^{m−1}} + 1` by hand yields the **antipodal
differential** `R_E = ∑_{j<N} ([j∈E] − [j+N∈E])·X^j`, whose coefficients lie in `{−1,0,1}`
and which is nonzero exactly when `E` is not antipodal-closed. The in-tree KKH26 resultant
engine (`not_isRoot_of_l1On_pow_lt`) then forbids `R_E(g) = 0` below the resultant bound,
and `∑ g^e = R_E(g)` by `g^N = −1`.

Together with the char-0 tower (`tower_closed_of_dyadic_sums_zero`) this pins the depth-1
finite-field classification: below the threshold, the halo is the priced O149 norm-divisor
object; above it, the halo is **provably empty**.

## References
* Issue #357 (surface (ii)); DISPROOF_LOG O145/O149; [KKH26] Lemma 1 machinery.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset ArkLib.ProximityGap.KKH26

/-- The antipodal differential of an exponent set `E ⊆ [0, 2N)`: the polynomial
`∑_{j<N} ([j∈E] − [j+N∈E])·X^j` — the by-hand reduction of `∑_{e∈E} X^e` modulo
`X^N + 1`. -/
noncomputable def antipodalDiff (N : ℕ) (E : Finset ℕ) : Polynomial ℤ :=
  ∑ j ∈ range N,
    C ((if j ∈ E then (1 : ℤ) else 0) - (if j + N ∈ E then (1 : ℤ) else 0)) * X ^ j

/-- `E` is antipodal-closed in `[0, 2N)`: membership is invariant under `j ↔ j + N`. -/
def AntipodalClosed (N : ℕ) (E : Finset ℕ) : Prop :=
  ∀ j < N, (j ∈ E ↔ j + N ∈ E)

theorem antipodalDiff_coeff (N : ℕ) (E : Finset ℕ) {j : ℕ} (hj : j < N) :
    (antipodalDiff N E).coeff j
      = (if j ∈ E then (1 : ℤ) else 0) - (if j + N ∈ E then (1 : ℤ) else 0) := by
  classical
  unfold antipodalDiff
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · by_cases h1 : j ∈ E <;> by_cases h2 : j + N ∈ E <;>
      simp [h1, h2, coeff_X_pow]
  · intro b _ hb
    have hne : j ≠ b := Ne.symm hb
    by_cases h1 : b ∈ E <;> by_cases h2 : b + N ∈ E <;>
      simp [h1, h2, coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

theorem antipodalDiff_coeff_of_ge (N : ℕ) (E : Finset ℕ) {j : ℕ} (hj : N ≤ j) :
    (antipodalDiff N E).coeff j = 0 := by
  classical
  unfold antipodalDiff
  rw [finset_sum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbN : b < N := Finset.mem_range.mp hb
  have hne : j ≠ b := by omega
  by_cases h1 : b ∈ E <;> by_cases h2 : b + N ∈ E <;>
    simp [h1, h2, coeff_X_pow, hne]

/-- The antipodal differential vanishes iff `E` is antipodal-closed. -/
theorem antipodalDiff_eq_zero_iff (N : ℕ) (E : Finset ℕ) :
    antipodalDiff N E = 0 ↔ AntipodalClosed N E := by
  constructor
  · intro h j hj
    have := antipodalDiff_coeff N E hj
    rw [h, coeff_zero] at this
    by_cases h1 : j ∈ E <;> by_cases h2 : j + N ∈ E <;> simp_all
  · intro h
    ext j
    rw [coeff_zero]
    rcases Nat.lt_or_ge j N with hj | hj
    · rw [antipodalDiff_coeff N E hj]
      by_cases h1 : j ∈ E
      · rw [if_pos h1, if_pos ((h j hj).mp h1), sub_self]
      · rw [if_neg h1, if_neg (fun hc => h1 ((h j hj).mpr hc)), sub_self]
    · exact antipodalDiff_coeff_of_ge N E hj

theorem antipodalDiff_natDegree_lt {N : ℕ} (hN : 0 < N) (E : Finset ℕ) :
    (antipodalDiff N E).natDegree < N := by
  rcases eq_or_ne (antipodalDiff N E) 0 with h | h
  · rw [h, natDegree_zero]; exact hN
  · by_contra hge
    have hlc : (antipodalDiff N E).coeff (antipodalDiff N E).natDegree ≠ 0 := by
      rw [← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr h
    exact hlc (antipodalDiff_coeff_of_ge N E (by omega))

theorem l1On_antipodalDiff_le (N : ℕ) (E : Finset ℕ) :
    l1On N (antipodalDiff N E) ≤ N := by
  unfold l1On
  calc ∑ j ∈ range N, ((antipodalDiff N E).coeff j).natAbs
      ≤ ∑ _j ∈ range N, 1 := by
        refine Finset.sum_le_sum ?_
        intro j hj
        rw [antipodalDiff_coeff N E (Finset.mem_range.mp hj)]
        by_cases h1 : j ∈ E <;> by_cases h2 : j + N ∈ E <;> simp [h1, h2]
    _ = N := by simp

/-- **Evaluation identity:** for `E ⊆ [0, 2N)` and `g` with `g^N = −1`,
`∑_{e∈E} g^e = (antipodalDiff N E)(g)`. -/
theorem sum_pow_eq_antipodalDiff_eval {F : Type*} [CommRing F] {g : F} {N : ℕ}
    (hgN : g ^ N = -1) {E : Finset ℕ} (hE : E ⊆ range (2 * N)) :
    ∑ e ∈ E, g ^ e
      = ((antipodalDiff N E).map (Int.castRingHom F)).eval g := by
  classical
  -- LHS as an indicator sum over the full range, then split `[0, 2N) = [0, N) ⊔ [N, 2N)`.
  have hsum0 : ∑ e ∈ E, g ^ e = ∑ e ∈ range (2 * N), if e ∈ E then g ^ e else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hE]
  have hsplit2 : (∑ e ∈ range (2 * N), if e ∈ E then g ^ e else 0)
      = (∑ j ∈ range N, if j ∈ E then g ^ j else 0)
        + ∑ j ∈ range N, if j + N ∈ E then g ^ (j + N) else 0 := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun e => if e ∈ E then g ^ e else 0)
        (Nat.zero_le N) (by omega : N ≤ 2 * N)]
    congr 1
    · rw [← Finset.range_eq_Ico]
    · rw [Finset.sum_Ico_eq_sum_range]
      have h2NN : 2 * N - N = N := by omega
      rw [h2NN]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Nat.add_comm N j]
  -- RHS: evaluate the differential termwise.
  have heval : ((antipodalDiff N E).map (Int.castRingHom F)).eval g
      = ∑ j ∈ range N,
          ((if j ∈ E then g ^ j else 0) - (if j + N ∈ E then g ^ j else 0)) := by
    unfold antipodalDiff
    rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    by_cases h1 : j ∈ E <;> by_cases h2 : j + N ∈ E <;> simp [h1, h2] <;> ring
  rw [hsum0, hsplit2, heval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hgjN : g ^ (j + N) = -g ^ j := by
    rw [pow_add, hgN]
    ring
  by_cases h2 : j + N ∈ E <;> simp [h2, hgjN] <;> ring

/-- **THE HALO-FREE THRESHOLD (depth 1).** For a prime `p` above the explicit resultant
threshold and a primitive `2^m`-th root `g ∈ F_p`: a subset `E ⊆ [0, 2^m)` has
`∑_{e∈E} g^e = 0` **iff** it is antipodal-closed. In particular the depth-1 halo is
provably EMPTY above the threshold — the finite-field census equals the char-0 census. -/
theorem sum_pow_eq_zero_iff_antipodalClosed {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ m))
    (hp : ((2 : ℕ) ^ (m - 1)) ^ 2 ^ (m - 1) < p) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E := by
  classical
  set N : ℕ := 2 ^ (m - 1) with hN
  have hNpos : 0 < N := by positivity
  have h2N : 2 * N = 2 ^ m := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  have hgN : g ^ N = -1 := by
    have := R12.pow_half_eq_neg_one hm hg
    simpa [hN] using this
  have hE' : E ⊆ range (2 * N) := by rwa [h2N]
  have heval := sum_pow_eq_antipodalDiff_eval hgN hE'
  constructor
  · intro hsum
    by_contra hnot
    have hR0 : antipodalDiff N E ≠ 0 := by
      intro h
      exact hnot ((antipodalDiff_eq_zero_iff N E).mp h)
    have hdeg : (antipodalDiff N E).natDegree < N := antipodalDiff_natDegree_lt hNpos E
    have hl1 : l1On N (antipodalDiff N E) ^ N < p := by
      calc l1On N (antipodalDiff N E) ^ N ≤ N ^ N := by
            exact Nat.pow_le_pow_left (l1On_antipodalDiff_le N E) N
        _ < p := by simpa [hN] using hp
    have := not_isRoot_of_l1On_pow_lt hm hg hR0 (by simpa [hN] using hdeg)
      (by simpa [hN] using hl1)
    apply this
    rw [Polynomial.IsRoot.def, ← heval]
    exact hsum
  · intro hclosed
    rw [heval, (antipodalDiff_eq_zero_iff N E).mpr hclosed]
    simp

/-! ## Source audit -/

#print axioms antipodalDiff_eq_zero_iff
#print axioms sum_pow_eq_antipodalDiff_eval
#print axioms sum_pow_eq_zero_iff_antipodalClosed

end ArkLib.ProximityGap.KKH26
