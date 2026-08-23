/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26SumsOfRootsOfUnity
import ArkLib.Data.CodingTheory.ProximityGap.E2VanishEnergy

/-!
# Char-`p` rigidity of the `e₂ = 0` locus (#407 — ATTACK-E2 / Approach F)

The prize-regime open core (issue #407, face B) is the **char-`p` transfer** of the char-`0`
`e₂ = 0` structure to the prize prime: *when does `p ∤` the relevant resultant/norm, so the
char-`0` vanishing structure persists mod `p` (no extra mod-`p` coincidences)?*

For a subset `S ⊆ μ_n` (`n = 2^k`), written through its exponents `U ⊆ range(2^k)`
(`S = {ζ^i : i ∈ U}`), the bad-scalar condition `e₂(S) = 0` is, by `E2VanishEnergy.e2_zero_iff`
(char `≠ 2`, Newton), exactly

  `e₁(S)² = p₂(S)`,  i.e.  `(∑_{i∈U} ζ^i)² = ∑_{i∈U} ζ^{2i}`.

This is the vanishing at `ζ` of the **integer** relation polynomial
`R_U(X) = (∑_{i∈U} X^i)² − ∑_{i∈U} X^{2i}` modulo `Φ_{2^k}(X) = X^{2^{k−1}} + 1`. We build the
**column-collapse fold** `e2Fold k U` — the canonical degree-`< 2^{k−1}` integer representative,
obtained by collapsing each coefficient of the raw relation onto its residue column mod
`2^{k−1}` with the alternating sign of `ζ^{2^{k−1}} = −1`. We prove it faithful at every
primitive `2^k`-th root of any field (`e2Fold_eval`) and bound its `ℓ¹` mass by
`l1On(R_U) ≤ (card U)² + card U` (`l1On_e2Fold_le`; the column collapse is `ℓ¹`-nonincreasing).

The resultant engine `KKH26.not_isRoot_of_l1On_pow_lt` then gives the **rigidity transfer**:

> **`e2_zero_rigidity_modp`** — if the folded relation is nonzero in characteristic `0`
> (i.e. `e₂(S) ≠ 0` over `ℂ`) and `p > ((card U)² + card U)^{2^{k−1}}`, then
> `e₁(S)² ≠ p₂(S)` over `F_p`, i.e. `e₂(S) ≠ 0` over `F_p`: **no extra mod-`p` solution.**

and its contrapositive census form

> **`e2_extra_solution_threshold`** — a *new* mod-`p` `e₂ = 0` solution (one not present in
> char `0`) forces `p ≤ (n² + n)^{n/2}`. Above that explicit threshold the `e₂ = 0` subsets over
> `F_p` are **exactly** the char-`0` ones, so the extremal-radius `e₂ = 0` count (and its
> `e₁`-dilation orbit count `K`) is the char-`0` count — an absolute, `q`-independent constant.

## The threshold `c` (honest scope)

The bound `c := (n² + n)^{n/2}` is the **crude resultant bound** (the same species as the
pair-sum threshold `4^{2^{k−1}}` of `PairSumRigidityModP`, but with `ℓ¹` mass `n²+n` in place of
`4`, since the quadratic `e₂`-relation has `O(n²)` cross terms rather than `4`). It is far from
sharp: the probe `scripts/probes/probe_407_e2_rigidity` measures the *true* crossover at
`p ≈ n³` (`β = 3`) — for `n = 16` the `e₂ = 0` count and `K` stabilize at `64 / K = 3` (the
char-`0` value) for every prime with `p ≳ n³`, and the actual bad primes all lie below `n³`.
So in the genuine prize regime `q ≈ n·2^{128} ≫ n³`, the rigidity holds with massive margin —
but a `sorry`-free Lean bound naturally lands the *provable* `c = (n²+n)^{n/2}` threshold;
sharpening `c` to the true `≈ n³` is a separate cyclotomic-norm-spectrum lane.

What this **does** establish unconditionally and uniformly in `n`: the char-`p` `e₂ = 0` locus
is *literally* the char-`0` locus for all `p` above an explicit, finite, `n`-dependent threshold
— i.e. there is **no BGK character-sum wall on this (algebraic) face**; the only obstruction is
the size of `c`, a pure cyclotomic-arithmetic quantity.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Polynomial Finset

namespace ArkLib.ProximityGap.E2VanishRigidityModP

open ArkLib.ProximityGap.KKH26

/-! ## The raw integer `e₂`-relation polynomial -/

/-- The raw integer relation polynomial of the `e₂ = 0` condition for the exponent set `U`:
`R_U(X) = (∑_{i ∈ U} X^i)² − ∑_{i ∈ U} X^{2i}`. Its vanishing at a primitive `n = 2^k`-th root
`ζ` is exactly `e₁(S)² = p₂(S)` for `S = {ζ^i : i ∈ U}`. -/
noncomputable def e2Rel (U : Finset ℕ) : Polynomial ℤ :=
  (∑ i ∈ U, X ^ i) ^ 2 - ∑ i ∈ U, X ^ (2 * i)

/-- `R_U` evaluated at any element `z` of any commutative ring (through the cast `ℤ → R`)
equals `(∑ z^i)² − ∑ z^{2i}`. -/
theorem e2Rel_eval {R : Type*} [CommRing R] (U : Finset ℕ) (z : R) :
    ((e2Rel U).map (Int.castRingHom R)).eval z
      = (∑ i ∈ U, z ^ i) ^ 2 - ∑ i ∈ U, z ^ (2 * i) := by
  unfold e2Rel
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sum, Polynomial.map_pow,
    Polynomial.map_X, eval_sub, eval_pow, eval_finset_sum, eval_pow, eval_X]

/-! ## The column-collapse fold to degree `< 2^{k−1}` -/

/-- The folded coefficient at column `t < 2^{k−1}`: collapse every raw coefficient
`R_U.coeff (t + 2·j·2^{k−1})` (sign `+`) and `R_U.coeff (t + (2j+1)·2^{k−1})` (sign `−`,
through `ζ^{2^{k−1}} = −1`) onto column `t`. The raw relation has degree `< 2·2^k = 8·2^{k−1}`,
so at most the columns `j ∈ {0,1,2,3,4,5,6,7}` contribute. -/
def foldCol (k : ℕ) (R : Polynomial ℤ) (t : ℕ) : ℤ :=
  ∑ j ∈ range (8), (if j % 2 = 0 then (1 : ℤ) else -1) * R.coeff (t + j * 2 ^ (k - 1))

/-- The folded `e₂`-relation: the canonical degree-`< 2^{k−1}` integer representative. -/
noncomputable def e2Fold (k : ℕ) (U : Finset ℕ) : Polynomial ℤ :=
  ∑ t ∈ range (2 ^ (k - 1)), C (foldCol k (e2Rel U) t) * X ^ t

theorem e2Fold_coeff (k : ℕ) (U : Finset ℕ) (t : ℕ) :
    (e2Fold k U).coeff t
      = if t < 2 ^ (k - 1) then foldCol k (e2Rel U) t else 0 := by
  rw [e2Fold, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases ht : t < 2 ^ (k - 1)
  · rw [if_pos ht, Finset.sum_eq_single_of_mem t (Finset.mem_range.mpr ht)
      (fun s _ hst => by simp [Ne.symm hst])]
    simp
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hst : t ≠ s := fun h => ht (h ▸ Finset.mem_range.mp hs)
    simp [hst]

theorem e2Fold_natDegree_lt (k : ℕ) (U : Finset ℕ) :
    (e2Fold k U).natDegree < 2 ^ (k - 1) := by
  by_cases h0 : e2Fold k U = 0
  · rw [h0]; simp
  · rw [Polynomial.natDegree_lt_iff_degree_lt h0, Polynomial.degree_lt_iff_coeff_zero]
    intro t ht
    rw [e2Fold_coeff]
    simp [not_lt.mpr (by exact_mod_cast ht : 2 ^ (k - 1) ≤ t)]

/-! ## The fold is faithful at primitive `2^k`-th roots -/

/-- A general column-collapse identity. For `ζ` with `ζ^h = −1` and any integer-coefficient
polynomial `R` of `natDegree < 8·h`, the value `R(ζ)` (through the cast `ℤ → L`) equals the
column-collapsed sum `∑_{t<h} (∑_{j<8} (−1)^j R.coeff(t+jh)) ζ^t`. Each raw monomial
`R.coeff e · ζ^e` lands, through `e = t + j·h` (`t = e % h`, `j = e / h`) and
`ζ^{t+jh} = (−1)^j ζ^t`, in column `t` with sign `(−1)^j`. -/
theorem foldCol_eval {L : Type*} [Field L] {h : ℕ} (hh : 0 < h) {ζ : L}
    (hζ : ζ ^ h = -1) {R : Polynomial ℤ} (hdeg : R.natDegree < 8 * h) :
    ∑ t ∈ range h, ((∑ j ∈ range 8,
        (if j % 2 = 0 then (1 : ℤ) else -1) * R.coeff (t + j * h) : ℤ) : L) * ζ ^ t
      = (R.map (Int.castRingHom L)).eval ζ := by
  have hpow : ∀ j t : ℕ, ζ ^ (t + j * h) = (if j % 2 = 0 then (1 : L) else -1) * ζ ^ t := by
    intro j t
    rw [pow_add, mul_comm j h, pow_mul, hζ]
    rcases Nat.even_or_odd j with hj | hj
    · rw [Even.neg_one_pow hj, Nat.even_iff.mp hj]; simp
    · rw [Odd.neg_one_pow hj, Nat.odd_iff.mp hj]; simp
  have hRHS : (R.map (Int.castRingHom L)).eval ζ
      = ∑ e ∈ range (8 * h), ((R.coeff e : ℤ) : L) * ζ ^ e := by
    rw [Polynomial.eval_eq_sum_range' (n := 8 * h)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.coeff_map]; rfl
  rw [hRHS]
  have hbij : ∑ e ∈ range (8 * h), ((R.coeff e : ℤ) : L) * ζ ^ e
      = ∑ t ∈ range h, ∑ j ∈ range 8,
          ((R.coeff (t + j * h) : ℤ) : L) * ζ ^ (t + j * h) := by
    rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun e => (e % h, e / h)) (fun p => p.1 + p.2 * h) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_range] at he ⊢
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hh), ?_⟩
      refine Finset.mem_range.mpr ?_
      rw [Nat.div_lt_iff_lt_mul hh]; omega
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      refine Finset.mem_range.mpr ?_
      obtain ⟨h1, h2⟩ := hp
      have hmul : p.2 * h ≤ 7 * h := Nat.mul_le_mul_right h (by omega)
      simp only []
      omega
    · intro e he
      simp only [Finset.mem_range] at he
      change e % h + e / h * h = e
      rw [Nat.mod_add_div']
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨h1, _⟩ := hp
      change ((p.1 + p.2 * h) % h, (p.1 + p.2 * h) / h) = p
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1,
        Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt h1, Nat.zero_add]
    · intro e he
      simp only [Finset.mem_range] at he
      change ((R.coeff e : ℤ) : L) * ζ ^ e
        = ((R.coeff (e % h + e / h * h) : ℤ) : L) * ζ ^ (e % h + e / h * h)
      rw [Nat.mod_add_div']
  rw [hbij]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpow j t]
  rcases Nat.even_or_odd j with hj | hj
  · rw [Nat.even_iff.mp hj]; push_cast; ring
  · rw [Nat.odd_iff.mp hj]; push_cast; ring

/-- **The fold is faithful.** At any primitive `2^k`-th root `ζ` of a field (`k ≥ 1`), the
folded `e₂`-relation evaluates to `e₁² − p₂ = (∑_{i∈U} ζ^i)² − ∑_{i∈U} ζ^{2i}`, provided every
exponent of `U` lies below `2^k`. -/
theorem e2Fold_eval {L : Type*} [Field L] {k : ℕ} (hk : 1 ≤ k) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) {U : Finset ℕ} (hU : ∀ i ∈ U, i < 2 ^ k) :
    ((e2Fold k U).map (Int.castRingHom L)).eval ζ
      = (∑ i ∈ U, ζ ^ i) ^ 2 - ∑ i ∈ U, ζ ^ (2 * i) := by
  have hhalf : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
    have h := pow_succ 2 (k - 1); rw [Nat.sub_add_cancel hk] at h; omega
  have hneg : ζ ^ (2 ^ (k - 1)) = -1 := by
    have hsq : (ζ ^ 2 ^ (k - 1)) ^ 2 = 1 := by
      rw [← pow_mul]
      have : 2 ^ (k - 1) * 2 = 2 ^ k := by omega
      rw [this]; exact hζ.pow_eq_one
    have hne : ζ ^ 2 ^ (k - 1) ≠ 1 :=
      hζ.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos (k - 1)).ne'
        (by have := hhalf; have := Nat.two_pow_pos (k - 1); omega)
    have hfac : (ζ ^ 2 ^ (k - 1) - 1) * (ζ ^ 2 ^ (k - 1) + 1) = 0 := by
      ring_nf; linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h) hne
    · linear_combination h
  have hdeg : (e2Rel U).natDegree < 8 * 2 ^ (k - 1) := by
    have hbound : (e2Rel U).natDegree < 2 * 2 ^ k := by
      unfold e2Rel
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
      apply max_lt
      · refine lt_of_le_of_lt (Polynomial.natDegree_pow_le) ?_
        have h1 : (∑ i ∈ U, (X : Polynomial ℤ) ^ i).natDegree < 2 ^ k := by
          refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
          refine (Finset.sup_lt_iff (by simp [Nat.two_pow_pos k] :
              ⊥ < 2 ^ k)).mpr fun i hi => ?_
          simp only [Function.comp_apply, Polynomial.natDegree_X_pow]
          exact hU i hi
        calc 2 * (∑ i ∈ U, (X : Polynomial ℤ) ^ i).natDegree
            ≤ 2 * (2 ^ k - 1) := by omega
          _ < 2 * 2 ^ k := by have := Nat.one_le_two_pow (n := k); omega
      · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
        refine (Finset.sup_lt_iff (by positivity : ⊥ < 2 * 2 ^ k)).mpr fun i hi => ?_
        simp only [Function.comp_apply, Polynomial.natDegree_X_pow]
        have := hU i hi; omega
    have hrw : 8 * 2 ^ (k - 1) = 4 * 2 ^ k := by rw [← hhalf]; ring
    have h2 : 2 * 2 ^ k ≤ 8 * 2 ^ (k - 1) := by
      rw [hrw]; have := Nat.one_le_two_pow (n := k); omega
    omega
  rw [← e2Rel_eval U ζ, ← foldCol_eval (Nat.two_pow_pos (k - 1)) hneg hdeg]
  unfold e2Fold
  rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow, eval_C, eval_X]
  rfl

/-! ## The `ℓ¹` mass of the fold is at most `(card U)² + card U` -/

/-- The `ℓ¹` mass of the folded `e₂`-relation is at most that of the raw relation: the
column-collapse is `ℓ¹`-nonincreasing (triangle inequality across the `8` columns, with the
injective reindexing `(t, j) ↦ t + j·h`). -/
theorem l1On_e2Fold_le_raw (k : ℕ) (U : Finset ℕ) :
    l1On (2 ^ (k - 1)) (e2Fold k U)
      ≤ ∑ e ∈ range (8 * 2 ^ (k - 1)), ((e2Rel U).coeff e).natAbs := by
  unfold l1On
  set h := 2 ^ (k - 1) with hh
  -- per-column triangle bound
  have hcol : ∀ t ∈ range h, ((e2Fold k U).coeff t).natAbs
      ≤ ∑ j ∈ range 8, ((e2Rel U).coeff (t + j * h)).natAbs := by
    intro t ht
    rw [e2Fold_coeff, if_pos (Finset.mem_range.mp ht)]
    show (foldCol k (e2Rel U) t).natAbs ≤ _
    unfold foldCol
    rw [← hh]
    refine le_trans (Int.natAbs_sum_le _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Int.natAbs_mul]
    have hunit : (if j % 2 = 0 then (1 : ℤ) else -1).natAbs = 1 := by
      rcases Nat.even_or_odd j with hj | hj
      · rw [Nat.even_iff.mp hj]; rfl
      · rw [Nat.odd_iff.mp hj]; rfl
    rw [hunit, one_mul]
  calc ∑ t ∈ range h, ((e2Fold k U).coeff t).natAbs
      ≤ ∑ t ∈ range h, ∑ j ∈ range 8, ((e2Rel U).coeff (t + j * h)).natAbs :=
        Finset.sum_le_sum hcol
    _ = ∑ p ∈ (range h) ×ˢ (range 8), ((e2Rel U).coeff (p.1 + p.2 * h)).natAbs := by
        rw [Finset.sum_product]
    _ = ∑ e ∈ ((range h) ×ˢ (range 8)).image (fun p => p.1 + p.2 * h),
          ((e2Rel U).coeff e).natAbs := by
        rw [Finset.sum_image]
        intro p hp q hq hpq
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hp hq
        simp only at hpq
        have hp1 := hp.1; have hq1 := hq.1
        -- from p.1 + p.2*h = q.1 + q.2*h with p.1,q.1 < h: equal quotients and remainders
        have hp1' : p.1 < h := hp1
        have hq1' : q.1 < h := hq1
        have hj : p.2 = q.2 := by
          by_contra hne
          rcases Nat.lt_or_ge p.2 q.2 with hlt | hge
          · have : p.1 + p.2 * h < q.2 * h := by
              have : (p.2 + 1) * h ≤ q.2 * h := Nat.mul_le_mul_right h hlt
              have hexp : (p.2 + 1) * h = p.2 * h + h := by ring
              omega
            omega
          · have hgt : q.2 < p.2 := lt_of_le_of_ne hge (fun h => hne h.symm)
            have : q.1 + q.2 * h < p.2 * h := by
              have : (q.2 + 1) * h ≤ p.2 * h := Nat.mul_le_mul_right h hgt
              have hexp : (q.2 + 1) * h = q.2 * h + h := by ring
              omega
            omega
        have hi : p.1 = q.1 := by
          rw [hj] at hpq; omega
        exact Prod.ext hi hj
    _ ≤ ∑ e ∈ range (8 * h), ((e2Rel U).coeff e).natAbs := by
        refine Finset.sum_le_sum_of_subset ?_
        intro e he
        simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at he
        obtain ⟨p, ⟨h1, h2⟩, rfl⟩ := he
        refine Finset.mem_range.mpr ?_
        have : p.2 * h ≤ 7 * h := Nat.mul_le_mul_right h (by omega)
        omega

/-- The two summands of the raw relation, named for the `ℓ¹` bound. -/
private noncomputable def sqPart (U : Finset ℕ) : Polynomial ℤ := (∑ i ∈ U, X ^ i) ^ 2
private noncomputable def powPart (U : Finset ℕ) : Polynomial ℤ := ∑ i ∈ U, X ^ (2 * i)

/-- Every coefficient of `(∑_{i∈U} X^i)²` is a nonnegative integer (it is a sum of products of
`0/1` coefficients). -/
private theorem sqPart_coeff_nonneg (U : Finset ℕ) (e : ℕ) : 0 ≤ (sqPart U).coeff e := by
  unfold sqPart
  rw [sq, Polynomial.coeff_mul]
  refine Finset.sum_nonneg fun p _ => ?_
  refine mul_nonneg ?_ ?_ <;>
  · rw [Polynomial.finset_sum_coeff]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Polynomial.coeff_X_pow]; split <;> norm_num

/-- Every coefficient of `∑_{i∈U} X^{2i}` is a nonnegative integer. -/
private theorem powPart_coeff_nonneg (U : Finset ℕ) (e : ℕ) : 0 ≤ (powPart U).coeff e := by
  unfold powPart
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Polynomial.coeff_X_pow]; split <;> norm_num

/-- The sum of all coefficients (eval at `1`) of `(∑_{i∈U} X^i)²` is `(card U)²`. -/
private theorem sqPart_eval_one (U : Finset ℕ) : (sqPart U).eval 1 = (U.card : ℤ) ^ 2 := by
  unfold sqPart
  rw [Polynomial.eval_pow, Polynomial.eval_finset_sum]
  simp [Polynomial.eval_pow, Polynomial.eval_X]

/-- The sum of all coefficients (eval at `1`) of `∑_{i∈U} X^{2i}` is `card U`. -/
private theorem powPart_eval_one (U : Finset ℕ) : (powPart U).eval 1 = (U.card : ℤ) := by
  unfold powPart
  rw [Polynomial.eval_finset_sum]
  simp [Polynomial.eval_pow, Polynomial.eval_X]

/-- For a polynomial with nonnegative integer coefficients, any partial coefficient sum over a
finset is at most its value at `1` (the total coefficient sum). -/
private theorem partial_coeff_sum_le_eval_one {P : Polynomial ℤ}
    (hP : ∀ e, 0 ≤ P.coeff e) (s : Finset ℕ) :
    ∑ e ∈ s, P.coeff e ≤ P.eval 1 := by
  have heval : P.eval 1 = ∑ e ∈ range (P.natDegree + 1), P.coeff e := by
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun e _ => by rw [one_pow, mul_one]
  rw [heval]
  -- restrict s to where coeffs are possibly nonzero
  calc ∑ e ∈ s, P.coeff e
      = ∑ e ∈ s ∩ range (P.natDegree + 1), P.coeff e := by
        rw [← Finset.sum_filter_add_sum_filter_not s (· ∈ range (P.natDegree + 1))]
        have hzero : ∑ e ∈ s.filter (fun e => e ∉ range (P.natDegree + 1)), P.coeff e = 0 := by
          refine Finset.sum_eq_zero fun e he => ?_
          simp only [Finset.mem_filter, Finset.mem_range, not_lt] at he
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hzero, add_zero, Finset.filter_mem_eq_inter]
    _ ≤ ∑ e ∈ range (P.natDegree + 1), P.coeff e :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun e _ _ => hP e)

/-- **The raw `ℓ¹` bound.** The total `ℓ¹` mass of the `e₂`-relation over the degree window is at
most `(card U)² + card U`: the square part contributes `(card U)²` (sum of its nonnegative
coefficients = value at `1`), the power-sum part `card U`. -/
theorem l1On_e2Fold_le (k : ℕ) (U : Finset ℕ) :
    l1On (2 ^ (k - 1)) (e2Fold k U) ≤ U.card ^ 2 + U.card := by
  refine le_trans (l1On_e2Fold_le_raw k U) ?_
  have hsplit : ∀ e, ((e2Rel U).coeff e).natAbs ≤ (sqPart U).coeff e + (powPart U).coeff e := by
    intro e
    have he : (e2Rel U).coeff e = (sqPart U).coeff e - (powPart U).coeff e := by
      unfold e2Rel sqPart powPart; rw [Polynomial.coeff_sub]
    rw [he]
    have h1 := sqPart_coeff_nonneg U e
    have h2 := powPart_coeff_nonneg U e
    have : ((sqPart U).coeff e - (powPart U).coeff e).natAbs
        ≤ (sqPart U).coeff e + (powPart U).coeff e := by
      rcases le_total ((powPart U).coeff e) ((sqPart U).coeff e) with hle | hle
      · rw [Int.natAbs_of_nonneg (by omega)]; omega
      · rw [show (sqPart U).coeff e - (powPart U).coeff e
              = -((powPart U).coeff e - (sqPart U).coeff e) by ring,
            Int.natAbs_neg, Int.natAbs_of_nonneg (by omega)]; omega
    exact_mod_cast this
  -- pass to ℤ and use the eval-at-1 totals
  have hcast : ((∑ e ∈ range (8 * 2 ^ (k - 1)), ((e2Rel U).coeff e).natAbs : ℕ) : ℤ)
      ≤ (U.card : ℤ) ^ 2 + U.card := by
    rw [Nat.cast_sum]
    calc ∑ e ∈ range (8 * 2 ^ (k - 1)), (((e2Rel U).coeff e).natAbs : ℤ)
        ≤ ∑ e ∈ range (8 * 2 ^ (k - 1)),
            ((sqPart U).coeff e + (powPart U).coeff e) := by
          refine Finset.sum_le_sum fun e _ => ?_
          exact_mod_cast hsplit e
      _ = (∑ e ∈ range (8 * 2 ^ (k - 1)), (sqPart U).coeff e)
          + ∑ e ∈ range (8 * 2 ^ (k - 1)), (powPart U).coeff e := by
          rw [Finset.sum_add_distrib]
      _ ≤ (sqPart U).eval 1 + (powPart U).eval 1 :=
          add_le_add (partial_coeff_sum_le_eval_one (sqPart_coeff_nonneg U) _)
            (partial_coeff_sum_le_eval_one (powPart_coeff_nonneg U) _)
      _ = (U.card : ℤ) ^ 2 + U.card := by rw [sqPart_eval_one, powPart_eval_one]
  exact_mod_cast hcast

/-! ## The rigidity transfer -/

/-- **The headline rigidity transfer.** Over `F_p` with a primitive `2^k`-th root `g`
(`k ≥ 1`), if the folded `e₂`-relation of an exponent set `U ⊆ range(2^k)` is **nonzero in
characteristic `0`** (i.e. `e₂(S) ≠ 0` over `ℂ`, captured by `e2Fold k U ≠ 0`) and `p` lies above
the explicit threshold `((card U)² + card U)^{2^{k−1}}`, then the `e₂ = 0` condition
`(∑_{i∈U} g^i)² = ∑_{i∈U} g^{2i}` **fails** over `F_p`: no extra mod-`p` `e₂ = 0` solution. -/
theorem e2_zero_rigidity_modp {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {U : Finset ℕ}
    (hU : ∀ i ∈ U, i < 2 ^ k) (hne0 : e2Fold k U ≠ 0)
    (hp : (U.card ^ 2 + U.card) ^ 2 ^ (k - 1) < p) :
    (∑ i ∈ U, g ^ i) ^ 2 ≠ ∑ i ∈ U, g ^ (2 * i) := by
  intro hzero
  -- `g` is a root of the folded relation mod `p`
  have hroot : ((e2Fold k U).map (Int.castRingHom (ZMod p))).IsRoot g := by
    unfold Polynomial.IsRoot
    rw [e2Fold_eval hk hg hU, hzero, sub_self]
  -- the threshold gate against `l1On`
  have hl1 : l1On (2 ^ (k - 1)) (e2Fold k U) ^ 2 ^ (k - 1) < p := by
    refine lt_of_le_of_lt ?_ hp
    exact Nat.pow_le_pow_left (l1On_e2Fold_le k U) _
  exact not_isRoot_of_l1On_pow_lt hk hg hne0 (e2Fold_natDegree_lt k U) hl1 hroot

/-- **The char-`0` nonvanishing input.** If `e₂(S) ≠ 0` over `ℂ` for `S = {ζ^i : i ∈ U}` at a
primitive complex `2^k`-th root, then the folded `e₂`-relation is a nonzero integer polynomial.
(Its complex evaluation is `e₂(S)·2`-up-to-sign nonzero; a zero polynomial would force it `0`.) -/
theorem e2Fold_ne_zero {k : ℕ} (hk : 1 ≤ k) {U : Finset ℕ} (hU : ∀ i ∈ U, i < 2 ^ k)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hC : (∑ i ∈ U, ζ ^ i) ^ 2 ≠ ∑ i ∈ U, ζ ^ (2 * i)) :
    e2Fold k U ≠ 0 := by
  intro h0
  apply hC
  have := e2Fold_eval hk hζ hU
  rw [h0] at this
  simp only [Polynomial.map_zero, Polynomial.eval_zero] at this
  linear_combination -this

/-- **Census form (contrapositive).** A subset `U ⊆ range(2^k)` whose `e₂ = 0` condition holds
over `F_p` but **not** over `ℂ` (a *new* mod-`p` solution) forces `p` below the explicit
threshold: `p ≤ ((card U)² + card U)^{2^{k−1}}`. Equivalently, above that threshold the `e₂ = 0`
subsets over `F_p` are exactly the char-`0` ones — the extremal-radius count is the (absolute,
`q`-independent) char-`0` count. -/
theorem e2_extra_solution_threshold {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ k)) {U : Finset ℕ}
    (hU : ∀ i ∈ U, i < 2 ^ k)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hCnz : (∑ i ∈ U, ζ ^ i) ^ 2 ≠ ∑ i ∈ U, ζ ^ (2 * i))
    (hFp : (∑ i ∈ U, g ^ i) ^ 2 = ∑ i ∈ U, g ^ (2 * i)) :
    p ≤ (U.card ^ 2 + U.card) ^ 2 ^ (k - 1) := by
  by_contra hgt
  rw [not_le] at hgt
  exact e2_zero_rigidity_modp hk hg hU (e2Fold_ne_zero hk hU hζ hCnz) hgt hFp

end ArkLib.ProximityGap.E2VanishRigidityModP

#print axioms ArkLib.ProximityGap.E2VanishRigidityModP.e2Fold_eval
#print axioms ArkLib.ProximityGap.E2VanishRigidityModP.l1On_e2Fold_le
#print axioms ArkLib.ProximityGap.E2VanishRigidityModP.e2_zero_rigidity_modp
#print axioms ArkLib.ProximityGap.E2VanishRigidityModP.e2Fold_ne_zero
#print axioms ArkLib.ProximityGap.E2VanishRigidityModP.e2_extra_solution_threshold
