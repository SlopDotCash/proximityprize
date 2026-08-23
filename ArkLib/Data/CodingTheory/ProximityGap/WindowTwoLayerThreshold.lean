/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity

/-!
# The two-layer law, hard half: window-census qualification at large primes forces
# characteristic-zero vanishing

Campaign #357, the formal core of probes O139–O143. The window-interior census of the
candidate-extremal (adjacent-pair monomial) family at constraint depth 1 asks, for a subset
`A` of exponents over the smooth domain `⟨g⟩` (`g` a primitive `2^m`-th root mod `p`),
whether the second elementary symmetric value

  `e₂(A, g) = ∑_{i<j ∈ A} g^(i+j)`

vanishes. Probes O139–O142 measured: the set of "qualifying" subsets is erratic in `p`, and
O141/O142 explained it completely — qualification at a prime outside an explicit finite set
forces a genuine characteristic-zero vanishing (Lam–Leung layer), and the exceptional primes
divide cyclotomic norms. This file formalizes the **hard half of that two-layer law**:

* `e2Folded m A` — the canonical representative of `e₂` as an integer polynomial of degree
  `< 2^(m-1)` (exponents folded through `X^(2^(m-1)) ≡ −1 mod Φ_{2^m}`), with coefficient
  vector `e2Coeff`;
* `e2Folded_eval` — folding is faithful: evaluating at any primitive `2^m`-th root of unity
  mod `p` recovers `e₂(A, g)`;
* `qualifying_implies_char0_vanishing` — **the threshold theorem**: if
  `(2^(m-1) · |A|²)^(2^(m-1)) < p` and `e₂(A, g) = 0` mod `p`, then `e2Folded m A = 0` —
  i.e. the vanishing already happens in `ℤ[ζ_{2^m}]`. Beyond the explicit threshold, the
  characteristic-`p` surplus layer is EMPTY: every qualifying subset is a classical
  vanishing-sum configuration.
* `e2_ne_zero_of_large_prime` — the consumable contrapositive: a subset whose folded
  polynomial is nonzero in characteristic zero cannot qualify at any prime above the
  threshold.

The engine is the in-tree Loop52/KKH26 resultant machinery
(`not_isRoot_of_l1On_pow_lt`: an integer polynomial of degree `< 2^(m-1)` with small
`ℓ¹`-norm cannot have a primitive `2^m`-th root of unity as a root mod a large prime).

## Honest scope

This is the census-side theorem. The bridge from the census to `mcaEvent` badness (the O138
algebra: a qualifying subset of size `a = k+2` yields a bad scalar for the adjacent-pair
stack at agreement `a`) is the named follow-up of the O138 formalization lane; this file
does not assert it. The char-0 emptiness at specific instances (probes: empty at all
`n = 16` depth-1 rows; 10 solutions at `(8,2)`) is likewise a separate, decidable statement
not consumed here.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
* Probes: `scripts/probes/probe_o141_norm_divisibility_spectrum.py`,
  `probe_o142_rate_quarter_spectrum.py`, `probe_o143_two_layer_law.py`; DISPROOF_LOG
  O139–O143. Issue #357.
* [KKH26] ePrint 2026/782 (the resultant/`ℓ¹` machinery formalized in
  `KKH26SumsOfRootsOfUnity.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-! ## The folded `e₂` polynomial -/

/-- The strictly-upper pairs of an exponent set. -/
def upperPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter (fun q => q.1 < q.2)

theorem upperPairs_card_le (A : Finset ℕ) : (upperPairs A).card ≤ A.card * A.card :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_product _ _))

/-- The `t`-th coefficient of the folded `e₂` polynomial: pairs whose exponent sum reduces
to `t` count `+1`, pairs reducing to `t + 2^(m-1)` count `−1` (the fold
`X^(2^(m-1)) ≡ −1`). -/
def e2Coeff (m : ℕ) (A : Finset ℕ) (t : ℕ) : ℤ :=
  (((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card : ℤ)
    - (((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card : ℤ)

/-- The folded `e₂` polynomial: the canonical degree-`< 2^(m-1)` representative of
`e₂({ζ^j : j ∈ A})` modulo `Φ_{2^m}`. -/
noncomputable def e2Folded (m : ℕ) (A : Finset ℕ) : Polynomial ℤ :=
  ∑ t ∈ range (2 ^ (m - 1)), C (e2Coeff m A t) * X ^ t

theorem e2Folded_coeff (m : ℕ) (A : Finset ℕ) (j : ℕ) :
    (e2Folded m A).coeff j = if j < 2 ^ (m - 1) then e2Coeff m A j else 0 := by
  rw [e2Folded, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hj : j < 2 ^ (m - 1)
  · rw [if_pos hj]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)
      (fun t _ htj => by simp [Ne.symm htj])]
    simp
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun t ht => ?_
    have htj : j ≠ t := fun h => hj (h ▸ Finset.mem_range.mp ht)
    simp [htj]

theorem e2Folded_natDegree_lt (m : ℕ) (A : Finset ℕ) :
    (e2Folded m A).natDegree < 2 ^ (m - 1) := by
  by_cases h0 : e2Folded m A = 0
  · rw [h0]
    simpa using pow_pos (by norm_num : (0 : ℕ) < 2) (m - 1)
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [e2Folded_coeff]
    have : ¬ j < 2 ^ (m - 1) := not_lt.mpr (by exact_mod_cast hj)
    simp [this]

/-- The `ℓ¹` mass of the folded polynomial is at most `2^(m-1) · |A|²` (crude but
explicit). -/
theorem l1On_e2Folded_le (m : ℕ) (A : Finset ℕ) :
    l1On (2 ^ (m - 1)) (e2Folded m A) ≤ 2 ^ (m - 1) * (A.card * A.card) := by
  unfold l1On
  calc ∑ j ∈ range (2 ^ (m - 1)), ((e2Folded m A).coeff j).natAbs
      ≤ ∑ _j ∈ range (2 ^ (m - 1)), A.card * A.card := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [e2Folded_coeff, if_pos (Finset.mem_range.mp hj)]
        have h1 : ((upperPairs A).filter
            (fun q => (q.1 + q.2) % 2 ^ m = j)).card ≤ A.card * A.card :=
          le_trans (Finset.card_filter_le _ _) (upperPairs_card_le A)
        have h2 : ((upperPairs A).filter
            (fun q => (q.1 + q.2) % 2 ^ m = j + 2 ^ (m - 1))).card ≤ A.card * A.card :=
          le_trans (Finset.card_filter_le _ _) (upperPairs_card_le A)
        unfold e2Coeff
        omega
    _ = 2 ^ (m - 1) * (A.card * A.card) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-! ## Folding is faithful at primitive `2^m`-th roots -/

/-- Evaluating the folded polynomial at a primitive `2^m`-th root of unity mod `p` recovers
the census quantity `e₂(A, g) = ∑_{i<j ∈ A} g^(i+j)`. -/
theorem e2Folded_eval {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ) :
    ((e2Folded m A).map (Int.castRingHom (ZMod p))).eval g
      = ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) := by
  classical
  have hord : orderOf g = 2 ^ m := (hg.eq_orderOf).symm
  have hhalf : g ^ (2 ^ (m - 1)) = -1 := pow_half_eq_neg_one hm hg
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  -- LHS: the coefficient-vector form
  have hLHS : ((e2Folded m A).map (Int.castRingHom (ZMod p))).eval g
      = ∑ t ∈ range (2 ^ (m - 1)), ((e2Coeff m A t : ZMod p)) * g ^ t := by
    rw [e2Folded, Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow, eval_C,
      eval_X]
    norm_cast
  -- RHS: reduce each exponent mod 2^m, then fold the upper half through g^(2^(m-1)) = −1.
  have hpow_mod : ∀ e : ℕ, g ^ e = g ^ (e % 2 ^ m) := by
    intro e
    conv_lhs => rw [← Nat.div_add_mod e (2 ^ m)]
    rw [pow_add, pow_mul, hg.pow_eq_one, one_pow, one_mul]
  have hfold : ∀ e : ℕ, e < 2 ^ m → 2 ^ (m - 1) ≤ e →
      g ^ e = -(g ^ (e - 2 ^ (m - 1))) := by
    intro e _ hge
    have : g ^ e = g ^ (e - 2 ^ (m - 1)) * g ^ (2 ^ (m - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, hhalf, mul_neg_one]
  -- group the pair sum by folded exponent
  have hRHS : ∑ q ∈ upperPairs A, g ^ (q.1 + q.2)
      = ∑ t ∈ range (2 ^ (m - 1)), ((e2Coeff m A t : ZMod p)) * g ^ t := by
    have hmaps : ∀ q ∈ upperPairs A,
        (if (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) then (q.1 + q.2) % 2 ^ m
         else (q.1 + q.2) % 2 ^ m - 2 ^ (m - 1)) ∈ range (2 ^ (m - 1)) := by
      intro q _
      by_cases hc : (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1)
      · simpa [hc] using hc
      · have hlt : (q.1 + q.2) % 2 ^ m < 2 ^ m :=
          Nat.mod_lt _ (by positivity)
        simp only [hc, if_false, Finset.mem_range]
        omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun q => g ^ (q.1 + q.2))]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htlt : t < 2 ^ (m - 1) := Finset.mem_range.mp ht
    -- the fiber over t splits into the +1 part (residue t) and the −1 part (residue t+h)
    have hfiber : (upperPairs A).filter (fun q =>
        (if (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) then (q.1 + q.2) % 2 ^ m
         else (q.1 + q.2) % 2 ^ m - 2 ^ (m - 1)) = t)
      = (upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)
        ∪ (upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hq, hfold⟩
        by_cases hc : (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1)
        · left; exact ⟨hq, by simpa [hc] using hfold⟩
        · right
          refine ⟨hq, ?_⟩
          rw [if_neg hc] at hfold
          omega
      · rintro (⟨hq, hr⟩ | ⟨hq, hr⟩)
        · exact ⟨hq, by simp [hr, htlt]⟩
        · refine ⟨hq, ?_⟩
          have hc : ¬ (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) := by omega
          rw [if_neg hc, hr]
          omega
    have hdisj : Disjoint
        ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t))
        ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))) := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      omega
    rw [hfiber, Finset.sum_union hdisj]
    -- the +1 part: every term is g^t
    have hplus : ∑ q ∈ (upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t),
        g ^ (q.1 + q.2)
        = (((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card : ZMod p)
          * g ^ t := by
      rw [Finset.sum_congr rfl (fun q hq => ?_), Finset.sum_const, nsmul_eq_mul]
      have hr := (Finset.mem_filter.mp hq).2
      rw [hpow_mod, hr]
    -- the −1 part: every term is −g^t
    have hminus : ∑ q ∈ (upperPairs A).filter
          (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1)),
        g ^ (q.1 + q.2)
        = -((((upperPairs A).filter
            (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card : ZMod p) * g ^ t) := by
      rw [Finset.sum_congr rfl (fun q hq => ?_), Finset.sum_neg_distrib, Finset.sum_const,
        nsmul_eq_mul]
      have hr := (Finset.mem_filter.mp hq).2
      have hlt : (q.1 + q.2) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
      rw [hpow_mod, hfold _ hlt (by omega)]
      congr 1
      rw [hr]
      congr 1
      omega
    rw [hplus, hminus, e2Coeff]
    push_cast
    ring
  rw [hLHS, hRHS]

/-! ## The threshold theorem -/

/-- **The two-layer law, hard half (#357 O141 principle, formal).** If the prime is above
the explicit threshold `(2^(m-1)·|A|²)^(2^(m-1))` and the census quantity
`e₂(A, g) = ∑_{i<j∈A} g^(i+j)` vanishes mod `p`, then the folded `e₂` polynomial already
vanishes in characteristic zero — qualification at large primes forces a classical
vanishing-sum configuration; the characteristic-`p` surplus layer is empty beyond the
threshold. -/
theorem qualifying_implies_char0_vanishing {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ)
    (hp : (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) < p)
    (hzero : ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) = 0) :
    e2Folded m A = 0 := by
  by_contra hR0
  have hdeg := e2Folded_natDegree_lt m A
  have hl1 : l1On (2 ^ (m - 1)) (e2Folded m A) ^ 2 ^ (m - 1) < p := by
    calc l1On (2 ^ (m - 1)) (e2Folded m A) ^ 2 ^ (m - 1)
        ≤ (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) :=
          Nat.pow_le_pow_left (l1On_e2Folded_le m A) _
      _ < p := hp
  have hnoroot := not_isRoot_of_l1On_pow_lt hm hg hR0 hdeg hl1
  apply hnoroot
  unfold Polynomial.IsRoot
  rw [e2Folded_eval hm hg A, hzero]

/-- **The consumable contrapositive**: a subset whose folded `e₂` polynomial is nonzero in
characteristic zero cannot qualify (have `e₂(A, g) = 0`) at any prime above the explicit
threshold. Combined with the probe-verified char-0 emptiness at the `n = 16` depth-1 rows,
this is the formal "clean at all large fields" statement for the candidate-extremal
family's mid-window census. -/
theorem e2_ne_zero_of_large_prime {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ)
    (hR0 : e2Folded m A ≠ 0)
    (hp : (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) < p) :
    ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) ≠ 0 :=
  fun hzero => hR0 (qualifying_implies_char0_vanishing hm hg A hp hzero)

/-! ## The parity law (O144): `a ≡ 2 (mod 4)` kills the characteristic-zero layer

The coefficient sum of the folded polynomial is congruent mod 2 to the total pair count
(each pair contributes `±1` to exactly one folded coefficient), so `e2Folded = 0` forces
`C(|A|, 2)` even. At the depth-1 census row `a = k + 2` this is exactly the production
dimensions `k ≡ 0 (mod 4)`: their char-0 layer is empty at every smooth scale, uniformly,
with no enumeration. -/

section Parity

/-- The fold partition: summing both residue-filter cardinalities over the folded range
recovers the total pair count (each pair's reduced exponent lies in exactly one filter at
exactly one `t`). -/
theorem sum_filter_cards (m : ℕ) (hm : 1 ≤ m) (A : Finset ℕ) :
    ∑ t ∈ range (2 ^ (m - 1)),
      (((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card
        + ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card)
      = (upperPairs A).card := by
  classical
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hmaps : ∀ q ∈ upperPairs A,
      (if (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) then (q.1 + q.2) % 2 ^ m
       else (q.1 + q.2) % 2 ^ m - 2 ^ (m - 1)) ∈ range (2 ^ (m - 1)) := by
    intro q _
    by_cases hc : (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1)
    · simpa [hc] using hc
    · have hlt : (q.1 + q.2) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
      simp only [hc, if_false, Finset.mem_range]
      omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htlt : t < 2 ^ (m - 1) := Finset.mem_range.mp ht
  have hfiber : (upperPairs A).filter (fun q =>
      (if (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) then (q.1 + q.2) % 2 ^ m
       else (q.1 + q.2) % 2 ^ m - 2 ^ (m - 1)) = t)
    = (upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)
      ∪ (upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hq, hfold⟩
      by_cases hc : (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1)
      · left; exact ⟨hq, by simpa [hc] using hfold⟩
      · right
        refine ⟨hq, ?_⟩
        rw [if_neg hc] at hfold
        omega
    · rintro (⟨hq, hr⟩ | ⟨hq, hr⟩)
      · exact ⟨hq, by simp [hr, htlt]⟩
      · refine ⟨hq, ?_⟩
        have hc : ¬ (q.1 + q.2) % 2 ^ m < 2 ^ (m - 1) := by omega
        rw [if_neg hc, hr]
        omega
  have hdisj : Disjoint
      ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t))
      ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    omega
  rw [hfiber, Finset.card_union_of_disjoint hdisj]

/-- **The parity obstruction (O144, formal).** If the pair count `C(|A|,2)` is odd, the
folded `e₂` polynomial cannot vanish: summing its coefficients gives the pair count mod 2. -/
theorem e2Folded_ne_zero_of_odd_pairs (m : ℕ) (hm : 1 ≤ m) (A : Finset ℕ)
    (hodd : ¬ 2 ∣ (upperPairs A).card) :
    e2Folded m A ≠ 0 := by
  intro h0
  apply hodd
  -- all folded coefficients vanish, so the integer coefficient sum is zero
  have hcoeffs : ∀ t ∈ range (2 ^ (m - 1)), e2Coeff m A t = 0 := by
    intro t ht
    have := e2Folded_coeff m A t
    rw [h0, Polynomial.coeff_zero] at this
    rw [if_pos (Finset.mem_range.mp ht)] at this
    exact this.symm
  have hsum0 : ∑ t ∈ range (2 ^ (m - 1)), e2Coeff m A t = 0 :=
    Finset.sum_eq_zero hcoeffs
  -- but the coefficient sum differs from the total pair count by an even number
  have hkey : ((upperPairs A).card : ℤ)
      = ∑ t ∈ range (2 ^ (m - 1)), e2Coeff m A t
        + 2 * ∑ t ∈ range (2 ^ (m - 1)),
            (((upperPairs A).filter
              (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card : ℤ) := by
    have hpart := sum_filter_cards m hm A
    have hcast : ((upperPairs A).card : ℤ)
        = ∑ t ∈ range (2 ^ (m - 1)),
            ((((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card : ℤ)
              + (((upperPairs A).filter
                  (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card : ℤ)) := by
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) hpart.symm
    rw [hcast]
    unfold e2Coeff
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsum0, zero_add] at hkey
  have hdvd : (2 : ℤ) ∣ ((upperPairs A).card : ℤ) := ⟨_, hkey⟩
  exact_mod_cast hdvd

/-- The strict-upper-pair count identity: `2 · #upperPairs = |A| · (|A| − 1)` (the
off-diagonal splits into the two strict halves, swapped onto each other). -/
theorem two_mul_upperPairs_card (A : Finset ℕ) :
    2 * (upperPairs A).card = A.card * (A.card - 1) := by
  classical
  have hswap : ((A ×ˢ A).filter (fun q => q.2 < q.1)).card = (upperPairs A).card := by
    refine Finset.card_bij' (fun q _ => (q.2, q.1)) (fun q _ => (q.2, q.1)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [upperPairs, Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro q hq
      simp only [upperPairs, Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
    · intro q _; rfl
    · intro q _; rfl
  have hunion : A.offDiag = upperPairs A ∪ (A ×ˢ A).filter (fun q => q.2 < q.1) := by
    ext q
    simp only [Finset.mem_offDiag, upperPairs, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨h1, h2, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, ne_of_gt h⟩
  have hdisj : Disjoint (upperPairs A) ((A ×ˢ A).filter (fun q => q.2 < q.1)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    exact absurd e2 (not_lt.mpr (le_of_lt e1))
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, hswap, Finset.offDiag_card] at hcard
  have hms : A.card * (A.card - 1) = A.card * A.card - A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · simp [h]
    · have h1 : A.card - 1 + 1 = A.card := Nat.succ_pred_eq_of_pos h
      calc A.card * (A.card - 1)
          = A.card * (A.card - 1) + A.card - A.card := by omega
        _ = A.card * (A.card - 1 + 1) - A.card := by rw [Nat.mul_succ]
        _ = A.card * A.card - A.card := by rw [h1]
  rw [hms, hcard]
  omega

/-- **The odd-pair-count rows are char-0 clean (general parity law).** For
`|A| ≡ 2` or `3 (mod 4)` — exactly the sizes with an odd pair count `C(|A|,2)` — no subset
can qualify at any prime above the explicit threshold: at every smooth scale `n = 2^m`,
uniformly, with no enumeration. -/
theorem e2_ne_zero_of_odd_row {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ)
    (hA : A.card % 4 = 2 ∨ A.card % 4 = 3)
    (hp : (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) < p) :
    ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) ≠ 0 := by
  refine e2_ne_zero_of_large_prime hm hg A ?_ hp
  refine e2Folded_ne_zero_of_odd_pairs m hm A ?_
  intro ⟨u, hu⟩
  have h2 := two_mul_upperPairs_card A
  obtain ⟨t, ht⟩ : ∃ t, A.card = 4 * t + 2 ∨ A.card = 4 * t + 3 := ⟨A.card / 4, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, t * t = s := ⟨_, rfl⟩
  rcases ht with ht | ht
  · -- `|A| = 4t + 2`: the pair count is `8t² + 6t + 1`, odd.
    have h1 : A.card - 1 = 4 * t + 1 := by omega
    rw [h1, ht] at h2
    have hodd : (4 * t + 2) * (4 * t + 1) = 2 * (8 * (t * t) + 6 * t + 1) := by ring
    rw [hodd, hs] at h2
    omega
  · -- `|A| = 4t + 3`: the pair count is `8t² + 10t + 3`, odd.
    have h1 : A.card - 1 = 4 * t + 2 := by omega
    rw [h1, ht] at h2
    have hodd : (4 * t + 3) * (4 * t + 2) = 2 * (8 * (t * t) + 10 * t + 3) := by ring
    rw [hodd, hs] at h2
    omega

/-- **Production dimensions are char-0 clean (O144 headline, formal).** For `|A| ≡ 2 (mod 4)`
(the depth-1 census row `a = k + 2` at every dimension `k ≡ 0 (mod 4)`, in particular all
`k = 2^j`, `j ≥ 2`), no subset can qualify at any prime above the explicit threshold — at
every smooth scale `n = 2^m`, uniformly, with no enumeration. -/
theorem e2_ne_zero_of_production_dim {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (A : Finset ℕ)
    (hA : A.card % 4 = 2)
    (hp : (2 ^ (m - 1) * (A.card * A.card)) ^ 2 ^ (m - 1) < p) :
    ∑ q ∈ upperPairs A, g ^ (q.1 + q.2) ≠ 0 :=
  e2_ne_zero_of_odd_row hm hg A (Or.inl hA) hp

end Parity

/-! ## Source audit -/

#print axioms e2Folded_eval
#print axioms qualifying_implies_char0_vanishing
#print axioms e2_ne_zero_of_large_prime
#print axioms e2Folded_ne_zero_of_odd_pairs
#print axioms e2_ne_zero_of_odd_row
#print axioms e2_ne_zero_of_production_dim

end ArkLib.ProximityGap.WindowTwoLayer
