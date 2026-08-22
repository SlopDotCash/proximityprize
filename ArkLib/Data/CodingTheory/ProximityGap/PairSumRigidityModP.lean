/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity
import ArkLib.Data.CodingTheory.ProximityGap.MCAVerticalStratumCharZero

/-!
# The vertical stratum's mod-p transfer surface, discharged: pair-sum rigidity over `F_p`
# above an explicit threshold

Campaign #357, round 10(a) follow-up. The vertical stratum of the wide-circuit census
closed in characteristic zero (`pair_sum_rigidity`: two non-antipodal root-of-unity pairs
of `μ_{2^k}` with equal sums coincide), with the mod-`p` side left as a *named* transfer
surface. This file discharges it, by the same species of weld as the two-layer threshold
law (`WindowTwoLayerThreshold`):

* `pairSumFolded k i j i' j'` — the 4-term pair-sum relation
  `ζ^i + ζ^j − ζ^{i'} − ζ^{j'}` folded to its canonical degree-`< 2^(k−1)` integer
  representative (exponents reduced through `X^(2^(k-1)) ≡ −1 mod Φ_{2^k}`), with
  `pairSumFolded_eval` (folding is faithful at every primitive `2^k`-th root of any
  field) and `l1On_pairSumFolded_le` (its `ℓ¹` mass is at most `4`).
* `pairSumFolded_ne_zero` — characteristic-zero nonvanishing is **not** redone
  combinatorially: it is `pair_sum_rigidity` itself, instantiated over `ℂ` through the
  fold's faithfulness.
* `pair_sum_rigidity_modp` — **the headline**: over `F_p` with a primitive `2^k`-th root
  and `p` above the explicit threshold `4^(2^(k−1))`, two non-antipodal distinct pairs
  with equal sums coincide — the resultant engine (`not_isRoot_of_l1On_pow_lt`) kills any
  mod-`p` collision whose folded relation survives in characteristic zero.
* `pair_sums_ne_modp` — the census-facing contrapositive: distinct non-antipodal pairs
  have **distinct sums** over `F_p` above the threshold, so the only multi-point vertical
  line of the configuration `Γ_n` is the degenerate `e = 0` and **the vertical stratum
  census is exactly `C(n/2, 3)` over `F_p`, uniformly in the scale** — the second stratum
  now closed on both sides (char 0 + mod-p transfer).

## Honest scope

The threshold `4^(2^(k−1))` is the crude resultant bound, far from sharp: the probe
(`scripts/probes/probe_pairsum_rigidity_modp.py`) measures the actual violation spectrum —
at `n = 8` the only violating prime is `17` (threshold `256`); at `n = 16` the violating
primes are `{17, 97, 113, 257, 337}` (threshold `65536`). Sharpening the threshold to the
true spectrum (the cyclotomic-norm divisors, O141-style) is a separate, finer lane; this
file establishes the *uniform* statement that the surface demanded.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 round 10(a) (`MCAVerticalStratumCharZero.lean`); the resultant engine in
  `KKH26SumsOfRootsOfUnity.lean`; the fold technique of `WindowTwoLayerThreshold.lean`.
* Probe: `scripts/probes/probe_pairsum_rigidity_modp.py` (V1 spectrum, V2 fold law,
  V3 `ℓ¹` mass — ALL PASS at `n = 4, 8, 16`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26
open ProximityGap.MCAVerticalStratumCharZero

namespace ArkLib.ProximityGap.PairSumRigidityModP

/-! ## The folded 4-term relation -/

/-- The signed fold indicator: exponent `a < 2^k` contributes `+1` at `t = a` (low half)
or `−1` at `t = a − 2^(k−1)` (high half, through `ζ^(2^(k−1)) = −1`). -/
def ind (k a t : ℕ) : ℤ :=
  (if a = t then 1 else 0) - (if a = t + 2 ^ (k - 1) then 1 else 0)

/-- The `t`-th coefficient of the folded pair-sum relation. -/
def foldCoeff (k i j i' j' t : ℕ) : ℤ :=
  ind k i t + ind k j t - ind k i' t - ind k j' t

/-- The folded pair-sum relation: the canonical degree-`< 2^(k−1)` integer representative
of `ζ^i + ζ^j − ζ^{i'} − ζ^{j'}` modulo `Φ_{2^k}`. -/
noncomputable def pairSumFolded (k i j i' j' : ℕ) : Polynomial ℤ :=
  ∑ t ∈ range (2 ^ (k - 1)), C (foldCoeff k i j i' j' t) * X ^ t

theorem pairSumFolded_coeff (k i j i' j' t : ℕ) :
    (pairSumFolded k i j i' j').coeff t
      = if t < 2 ^ (k - 1) then foldCoeff k i j i' j' t else 0 := by
  rw [pairSumFolded, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases ht : t < 2 ^ (k - 1)
  · rw [if_pos ht]
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_range.mpr ht)
      (fun s _ hst => by simp [Ne.symm hst])]
    simp
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hst : t ≠ s := fun h => ht (h ▸ Finset.mem_range.mp hs)
    simp [hst]

theorem pairSumFolded_natDegree_lt (k i j i' j' : ℕ) :
    (pairSumFolded k i j i' j').natDegree < 2 ^ (k - 1) := by
  by_cases h0 : pairSumFolded k i j i' j' = 0
  · rw [h0]
    simpa using pow_pos (by norm_num : (0 : ℕ) < 2) (k - 1)
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro t ht
    rw [pairSumFolded_coeff]
    have : ¬ t < 2 ^ (k - 1) := not_lt.mpr (by exact_mod_cast ht)
    simp [this]

/-! ## The `ℓ¹` mass is at most 4 -/

/-- Each exponent below `2^k` contributes total `ℓ¹` mass at most `1` to the fold. -/
theorem sum_natAbs_ind_le {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : a < 2 ^ k) :
    ∑ t ∈ range (2 ^ (k - 1)), (ind k a t).natAbs ≤ 1 := by
  have hsplit : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
    have h := pow_succ 2 (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    omega
  have hpt : ∀ t, (ind k a t).natAbs
      ≤ (if a = t then 1 else 0) + (if a = t + 2 ^ (k - 1) then 1 else 0) := by
    intro t
    unfold ind
    split <;> split <;> simp
  calc ∑ t ∈ range (2 ^ (k - 1)), (ind k a t).natAbs
      ≤ ∑ t ∈ range (2 ^ (k - 1)),
          ((if a = t then 1 else 0) + (if a = t + 2 ^ (k - 1) then 1 else 0)) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ ≤ 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
        by_cases hcase : a < 2 ^ (k - 1)
        · have h2 : ∑ t ∈ range (2 ^ (k - 1)),
              (if a = t + 2 ^ (k - 1) then 1 else 0) = 0 :=
            Finset.sum_eq_zero fun t _ => if_neg (by omega)
          rw [h2, if_pos (Finset.mem_range.mpr hcase)]
        · have hconv : ∀ t ∈ range (2 ^ (k - 1)),
              (if a = t + 2 ^ (k - 1) then (1 : ℕ) else 0)
                = (if a - 2 ^ (k - 1) = t then 1 else 0) := by
            intro t ht
            by_cases hca : a = t + 2 ^ (k - 1)
            · rw [if_pos hca, if_pos (by omega)]
            · rw [if_neg hca, if_neg (by omega)]
          rw [Finset.sum_congr rfl hconv, Finset.sum_ite_eq,
            if_neg (by simpa [Finset.mem_range] using hcase)]
          split <;> omega

/-- The `ℓ¹` mass of the folded pair-sum relation is at most `4`. -/
theorem l1On_pairSumFolded_le {k : ℕ} (hk : 1 ≤ k) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k) :
    l1On (2 ^ (k - 1)) (pairSumFolded k i j i' j') ≤ 4 := by
  unfold l1On
  calc ∑ t ∈ range (2 ^ (k - 1)), ((pairSumFolded k i j i' j').coeff t).natAbs
      = ∑ t ∈ range (2 ^ (k - 1)), (foldCoeff k i j i' j' t).natAbs := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [pairSumFolded_coeff, if_pos (Finset.mem_range.mp ht)]
    _ ≤ ∑ t ∈ range (2 ^ (k - 1)),
          ((ind k i t).natAbs + (ind k j t).natAbs + (ind k i' t).natAbs
            + (ind k j' t).natAbs) := by
        refine Finset.sum_le_sum fun t _ => ?_
        unfold foldCoeff
        calc (ind k i t + ind k j t - ind k i' t - ind k j' t).natAbs
            ≤ (ind k i t + ind k j t - ind k i' t).natAbs + (ind k j' t).natAbs :=
              Int.natAbs_sub_le _ _
          _ ≤ ((ind k i t + ind k j t).natAbs + (ind k i' t).natAbs)
              + (ind k j' t).natAbs := by
              gcongr
              exact Int.natAbs_sub_le _ _
          _ ≤ (((ind k i t).natAbs + (ind k j t).natAbs) + (ind k i' t).natAbs)
              + (ind k j' t).natAbs := by
              gcongr
              exact Int.natAbs_add_le _ _
    _ = (∑ t ∈ range (2 ^ (k - 1)), (ind k i t).natAbs)
        + (∑ t ∈ range (2 ^ (k - 1)), (ind k j t).natAbs)
        + (∑ t ∈ range (2 ^ (k - 1)), (ind k i' t).natAbs)
        + ∑ t ∈ range (2 ^ (k - 1)), (ind k j' t).natAbs := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
    _ ≤ 1 + 1 + 1 + 1 :=
        add_le_add (add_le_add (add_le_add (sum_natAbs_ind_le hk hi)
          (sum_natAbs_ind_le hk hj)) (sum_natAbs_ind_le hk hi'))
          (sum_natAbs_ind_le hk hj')

/-! ## Folding is faithful at primitive `2^k`-th roots of any field -/

/-- `ζ^(2^(k−1)) = −1` for a primitive `2^k`-th root of unity of any field (the
field-generic form of the prime-field lemma in `KKH26SumsOfRootsOfUnity`). -/
theorem pow_half_eq_neg_one_field {L : Type*} [Field L] {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) : ζ ^ (2 ^ (k - 1)) = -1 := by
  have hsplit : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
    have h := pow_succ 2 (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    omega
  have h2 : ζ ^ (2 ^ (k - 1)) * ζ ^ (2 ^ (k - 1)) = 1 := by
    rw [← pow_add, hsplit, hζ.pow_eq_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exfalso
    have h1 : (1 : ℕ) ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    exact hζ.pow_ne_one_of_pos_of_lt (by positivity) (by omega) h
  · exact h

/-- The single-exponent fold evaluates back to the original power. -/
theorem sum_ind_mul {L : Type*} [Field L] {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) {a : ℕ} (ha : a < 2 ^ k) :
    ∑ t ∈ range (2 ^ (k - 1)), ((ind k a t : ℤ) : L) * ζ ^ t = ζ ^ a := by
  have hsplit : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
    have h := pow_succ 2 (k - 1)
    rw [Nat.sub_add_cancel hk] at h
    omega
  have hhalf : ζ ^ (2 ^ (k - 1)) = -1 := pow_half_eq_neg_one_field hk hζ
  have hterm : ∀ t, ((ind k a t : ℤ) : L) * ζ ^ t
      = (if a = t then ζ ^ t else 0) - (if a = t + 2 ^ (k - 1) then ζ ^ t else 0) := by
    intro t
    by_cases h1 : a = t <;> by_cases h2 : a = t + 2 ^ (k - 1) <;>
      simp [ind, h1, h2] <;> ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_sub_distrib,
    Finset.sum_ite_eq]
  by_cases hcase : a < 2 ^ (k - 1)
  · have h2 : ∑ t ∈ range (2 ^ (k - 1)),
        (if a = t + 2 ^ (k - 1) then ζ ^ t else 0) = 0 :=
      Finset.sum_eq_zero fun t _ => if_neg (by omega)
    rw [h2, if_pos (Finset.mem_range.mpr hcase), sub_zero]
  · have hconv : ∀ t ∈ range (2 ^ (k - 1)),
        (if a = t + 2 ^ (k - 1) then ζ ^ t else 0)
          = (if a - 2 ^ (k - 1) = t then ζ ^ t else 0) := by
      intro t ht
      by_cases hca : a = t + 2 ^ (k - 1)
      · rw [if_pos hca, if_pos (by omega)]
      · rw [if_neg hca, if_neg (by omega)]
    have hmem : a - 2 ^ (k - 1) ∈ range (2 ^ (k - 1)) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_congr rfl hconv, Finset.sum_ite_eq, if_pos hmem,
      if_neg (by simpa [Finset.mem_range] using hcase)]
    have hpow : ζ ^ a = ζ ^ (a - 2 ^ (k - 1)) * ζ ^ (2 ^ (k - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, hhalf]
    ring

/-- **Fold faithfulness.** Evaluating the folded relation at a primitive `2^k`-th root of
unity of any field recovers `ζ^i + ζ^j − ζ^{i'} − ζ^{j'}`. -/
theorem pairSumFolded_eval {L : Type*} [Field L] {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k) :
    ((pairSumFolded k i j i' j').map (Int.castRingHom L)).eval ζ
      = ζ ^ i + ζ ^ j - ζ ^ i' - ζ ^ j' := by
  have hLHS : ((pairSumFolded k i j i' j').map (Int.castRingHom L)).eval ζ
      = ∑ t ∈ range (2 ^ (k - 1)), ((foldCoeff k i j i' j' t : ℤ) : L) * ζ ^ t := by
    rw [pairSumFolded, Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow,
      eval_C, eval_X]
    norm_cast
  have hsplit : ∀ t, ((foldCoeff k i j i' j' t : ℤ) : L) * ζ ^ t
      = ((ind k i t : ℤ) : L) * ζ ^ t + ((ind k j t : ℤ) : L) * ζ ^ t
        - ((ind k i' t : ℤ) : L) * ζ ^ t - ((ind k j' t : ℤ) : L) * ζ ^ t := by
    intro t
    unfold foldCoeff
    push_cast
    ring
  rw [hLHS, Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_ind_mul hk hζ hi, sum_ind_mul hk hζ hj, sum_ind_mul hk hζ hi',
    sum_ind_mul hk hζ hj']

/-! ## Characteristic-zero nonvanishing = `pair_sum_rigidity` over `ℂ` -/

/-- **Char-0 nonvanishing through the rigidity theorem.** If the two pairs do not match,
the folded relation is a nonzero integer polynomial: were it zero, its evaluation at a
complex primitive `2^k`-th root would equate the pair sums, and `pair_sum_rigidity`
would force the match. -/
theorem pairSumFolded_ne_zero {k : ℕ} (hk : 1 ≤ k) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j') (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hne : ¬ ((i = i' ∧ j = j') ∨ (i = j' ∧ j = i'))) :
    pairSumFolded k i j i' j' ≠ 0 := by
  classical
  intro h0
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ k) :=
    ⟨_, Complex.isPrimitiveRoot_exp (2 ^ k) (by positivity)⟩
  have heval := pairSumFolded_eval (L := ℂ) hk hζ hi hj hi' hj'
  rw [h0] at heval
  simp only [Polynomial.map_zero, Polynomial.eval_zero] at heval
  have hsum : ζ ^ i + ζ ^ j = ζ ^ i' + ζ ^ j' := by linear_combination -heval
  exact hne (pair_sum_rigidity hk hζ hi hj hi' hj' hij hij' hnaij hsum)

/-! ## The headline: mod-p pair-sum rigidity above the explicit threshold -/

/-- **MOD-P PAIR-SUM RIGIDITY (the vertical stratum's transfer surface, discharged).**
Over `F_p` with a primitive `2^k`-th root `g` and `p` above the explicit threshold
`4^(2^(k−1))`: two distinct-element pairs of exponents below `2^k`, the first
non-antipodal, with equal sums `g^i + g^j = g^{i'} + g^{j'}`, coincide. Any collision
not forced in characteristic zero would make the folded relation a nonzero integer
polynomial of degree `< 2^(k−1)` and `ℓ¹` mass `≤ 4` with a primitive root mod `p` —
killed by the resultant engine above the threshold. -/
theorem pair_sum_rigidity_modp {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j') (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hp : 4 ^ 2 ^ (k - 1) < p)
    (hsum : g ^ i + g ^ j = g ^ i' + g ^ j') :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  by_contra hne
  have hR0 : pairSumFolded k i j i' j' ≠ 0 :=
    pairSumFolded_ne_zero hk hi hj hi' hj' hij hij' hnaij hne
  have hdeg : (pairSumFolded k i j i' j').natDegree < 2 ^ (k - 1) :=
    pairSumFolded_natDegree_lt k i j i' j'
  have hl1 : l1On (2 ^ (k - 1)) (pairSumFolded k i j i' j') ^ 2 ^ (k - 1) < p :=
    lt_of_le_of_lt
      (Nat.pow_le_pow_left (l1On_pairSumFolded_le hk hi hj hi' hj') _) hp
  have hnoroot := not_isRoot_of_l1On_pow_lt hk hg hR0 hdeg hl1
  apply hnoroot
  unfold Polynomial.IsRoot
  rw [pairSumFolded_eval hk hg hi hj hi' hj']
  linear_combination hsum

/-- **The census-facing contrapositive.** Distinct non-antipodal pairs have distinct sums
over `F_p` above the threshold: the only multi-point vertical line of `Γ_n` is the
degenerate `e = 0`, so the vertical stratum census is exactly `C(n/2, 3)` over `F_p`,
uniformly in the scale. -/
theorem pair_sums_ne_modp {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j') (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hp : 4 ^ 2 ^ (k - 1) < p)
    (hne : ¬ ((i = i' ∧ j = j') ∨ (i = j' ∧ j = i'))) :
    g ^ i + g ^ j ≠ g ^ i' + g ^ j' :=
  fun hsum =>
    hne (pair_sum_rigidity_modp hk hg hi hj hi' hj' hij hij' hnaij hp hsum)

/-! ## The sharp spectrum law: violating primes divide the collision resultant

The uniform threshold `4^(2^(k−1))` is crude; the *true* violation spectrum is governed by
cyclotomic norms: any prime exhibiting a collision divides the **nonzero** integer
resultant `Res(pairSumFolded, Φ_{2^k})` — so the violating primes at each scale form an
explicit finite set, and `p ∤ Res` is a per-instance criterion valid at **every** `p > 4`
(no size threshold). Probe V4 verifies both halves on every measured violation
(n = 8: 8 violations at p = 17; n = 16: 448 violations at {17, 97, 113, 257, 337}). -/

open ArkLib.ProximityGap.ResultantLiftLoop52

/-- Each fold indicator has absolute value at most `1`. -/
theorem natAbs_ind_le_one (k a t : ℕ) : (ind k a t).natAbs ≤ 1 := by
  unfold ind
  split <;> split <;> simp

/-- Every coefficient of the folded relation has absolute value at most `4`. -/
theorem natAbs_coeff_pairSumFolded_le (k i j i' j' t : ℕ) :
    ((pairSumFolded k i j i' j').coeff t).natAbs ≤ 4 := by
  rw [pairSumFolded_coeff]
  split
  · unfold foldCoeff
    calc (ind k i t + ind k j t - ind k i' t - ind k j' t).natAbs
        ≤ (ind k i t + ind k j t - ind k i' t).natAbs + (ind k j' t).natAbs :=
          Int.natAbs_sub_le _ _
      _ ≤ ((ind k i t + ind k j t).natAbs + (ind k i' t).natAbs)
          + (ind k j' t).natAbs := by
          gcongr
          exact Int.natAbs_sub_le _ _
      _ ≤ (((ind k i t).natAbs + (ind k j t).natAbs) + (ind k i' t).natAbs)
          + (ind k j' t).natAbs := by
          gcongr
          exact Int.natAbs_add_le _ _
      _ ≤ ((1 + 1) + 1) + 1 :=
          add_le_add (add_le_add (add_le_add (natAbs_ind_le_one k i t)
            (natAbs_ind_le_one k j t)) (natAbs_ind_le_one k i' t))
            (natAbs_ind_le_one k j' t)
  · simp

/-- The leading coefficient of a nonzero folded relation survives mod any prime `p > 4`. -/
theorem leadingCoeff_pairSumFolded_ne_zero_mod {p : ℕ} [Fact p.Prime] (hp4 : 4 < p)
    {k i j i' j' : ℕ} (hR0 : pairSumFolded k i j i' j' ≠ 0) :
    (((pairSumFolded k i j i' j').leadingCoeff : ℤ) : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have hlc0 : (pairSumFolded k i j i' j').leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR0
  have hdvd : p ∣ ((pairSumFolded k i j i' j').leadingCoeff).natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h0
    simpa using this
  have hle : p ≤ ((pairSumFolded k i j i' j').leadingCoeff).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hlc0) hdvd
  have hb := natAbs_coeff_pairSumFolded_le k i j i' j'
    (pairSumFolded k i j i' j').natDegree
  rw [Polynomial.coeff_natDegree] at hb
  omega

/-- **THE SHARP SPECTRUM LAW.** A mod-`p` pair-sum collision not forced in characteristic
zero makes `p` a divisor of the **nonzero** integer resultant
`Res(pairSumFolded, Φ_{2^k})`: the violating primes at each scale are exactly contained in
an explicit finite set of cyclotomic-norm divisors (O141-species), with no size threshold
beyond `p > 4`. -/
theorem pair_sum_collision_dvd_resultant {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j') (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hp4 : 4 < p)
    (hne : ¬ ((i = i' ∧ j = j') ∨ (i = j' ∧ j = i')))
    (hsum : g ^ i + g ^ j = g ^ i' + g ^ j') :
    (p : ℤ) ∣ Polynomial.resultant (pairSumFolded k i j i' j') (cyclotomic (2 ^ k) ℤ)
      ∧ Polynomial.resultant (pairSumFolded k i j i' j') (cyclotomic (2 ^ k) ℤ) ≠ 0 := by
  have hR0 : pairSumFolded k i j i' j' ≠ 0 :=
    pairSumFolded_ne_zero hk hi hj hi' hj' hij hij' hnaij hne
  refine ⟨?_, resultant_int_ne_zero_of_isCoprime_rat _ _
    (diff_coprime_cyclotomic_rat hk _ (pairSumFolded_natDegree_lt k i j i' j') hR0)⟩
  apply prime_dvd_resultant_of_common_root (α := g)
  · exact leadingCoeff_pairSumFolded_ne_zero_mod hp4 hR0
  · rw [(cyclotomic.monic (2 ^ k) ℤ).leadingCoeff]
    simp
  · unfold Polynomial.IsRoot
    rw [pairSumFolded_eval hk hg hi hj hi' hj']
    linear_combination hsum
  · rw [Polynomial.map_cyclotomic_int]
    exact hg.isRoot_cyclotomic (by positivity)

/-- **The per-instance sharp criterion**: at any prime `p > 4` with `p ∤ Res`, distinct
non-antipodal pairs have distinct sums — the threshold-free replacement of
`pair_sums_ne_modp`, decidable per scale by one integer-resultant computation. -/
theorem pair_sums_ne_of_not_dvd_resultant {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j') (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hp4 : 4 < p)
    (hnd : ¬ (p : ℤ) ∣ Polynomial.resultant (pairSumFolded k i j i' j')
      (cyclotomic (2 ^ k) ℤ))
    (hne : ¬ ((i = i' ∧ j = j') ∨ (i = j' ∧ j = i'))) :
    g ^ i + g ^ j ≠ g ^ i' + g ^ j' :=
  fun hsum => hnd (pair_sum_collision_dvd_resultant hk hg hi hj hi' hj' hij hij'
    hnaij hp4 hne hsum).1

/-! ## Source audit -/

#print axioms pairSumFolded_eval
#print axioms l1On_pairSumFolded_le
#print axioms pairSumFolded_ne_zero
#print axioms pair_sum_rigidity_modp
#print axioms pair_sums_ne_modp
#print axioms pair_sum_collision_dvd_resultant
#print axioms pair_sums_ne_of_not_dvd_resultant

end ArkLib.ProximityGap.PairSumRigidityModP
