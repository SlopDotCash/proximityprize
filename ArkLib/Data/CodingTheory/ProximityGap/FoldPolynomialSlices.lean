/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPow

/-!
# Fold branches of polynomial errors are coefficient slices (issue #232)

The branch-accounting program (DISPROOF_LOG O56–O59) tracks valued errors down the
2-adic tower via the even/odd folds `foldVal`/`foldValOdd`. This file proves that for a
**polynomial error** `e = f.eval` on a negation-closed domain (char ≠ 2, `0 ∉ D`), the
two branches are — up to the unit twist `y` — evaluations of the *coefficient slices*
of `f`:

* `eval_evenSlice` / `eval_oddSlice` — `f(x) + f(−x) = (evenSlice f)(x²)` and
  `f(x) − f(−x) = x·(oddSlice f)(x²)`, where `evenSlice f = contract 2 (f + f∘(−X))`
  collects the even-exponent coefficients (scaled by 2) and `oddSlice` the odd ones;
* `foldVal_polyeval` / `foldValOdd_polyeval` — `foldVal D f.eval (x₀²) = (evenSlice f)(x₀²)`
  and `foldValOdd D f.eval (x₀²) = x₀²·(oddSlice f)(x₀²)`;
* `foldVal_ne_zero_iff` / `foldValOdd_ne_zero_iff` — **branch aliveness = slice
  nonvanishing** (the twist drops out since `y ≠ 0`).

Since every valued error on a domain of size `n` interpolates to a unique polynomial of
degree `< n`, this translates the branch tree into plain coefficient combinatorics:
iterating, the depth-`ℓ` branches correspond to the residue classes of coefficient
exponents mod `2^ℓ` (under the ceiling-halving digit code: an odd fold maps exponent
`e ↦ (e+1)/2` because of the `y`-twist, an even fold maps `e ↦ e/2`), and a branch is
alive iff its class contains a nonzero coefficient — verified exhaustively at n = 16
(`scripts/probes/probe_fold_slices.py`). The open branch-count distribution question
(O59) is thereby the joint distribution of (evaluation weight, 2-adic coefficient
spread) over low-degree polynomials.
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F]

/-! Part 1: even/odd coefficient slices via expand/contract -/

theorem coeff_comp_neg_X (f : F[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, hp, hq, coeff_add]; ring
  | monomial k a =>
    have hC : ((-1 : F[X])) ^ k = C ((-1 : F) ^ k) := by
      rw [map_pow, map_neg, map_one]
    rw [monomial_comp, neg_pow, ← mul_assoc, hC, ← C_mul, coeff_C_mul, coeff_X_pow,
      coeff_monomial]
    by_cases h : n = k
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

theorem expand_contract_of_even_support {h : F[X]}
    (hodd : ∀ n, ¬ 2 ∣ n → h.coeff n = 0) :
    Polynomial.expand F 2 (Polynomial.contract 2 h) = h := by
  ext n
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hd : 2 ∣ n
  · rw [if_pos hd, coeff_contract (by norm_num : (2:ℕ) ≠ 0)]
    obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
    congr 1
    omega
  · rw [if_neg hd, hodd n hd]

/-- The even coefficient slice: `evenSlice f` collects the even-exponent coefficients,
scaled by 2 — `(evenSlice f).eval (x²) = f(x) + f(−x)`. -/
noncomputable def evenSlice (f : F[X]) : F[X] :=
  Polynomial.contract 2 (f + f.comp (-X))

/-- The odd coefficient slice: `(oddSlice f).eval (x²) · x = f(x) − f(−x)`. -/
noncomputable def oddSlice (f : F[X]) : F[X] :=
  Polynomial.contract 2 (Polynomial.divX (f - f.comp (-X)))

theorem eval_evenSlice (f : F[X]) (x : F) :
    (evenSlice f).eval (x ^ 2) = f.eval x + f.eval (-x) := by
  have hodd : ∀ n, ¬ 2 ∣ n → (f + f.comp (-X)).coeff n = 0 := by
    intro n hn
    rw [coeff_add, coeff_comp_neg_X]
    have hodd' : Odd n := Nat.odd_iff.mpr (by omega)
    rw [hodd'.neg_one_pow]
    ring
  have key := expand_contract_of_even_support hodd
  calc (evenSlice f).eval (x ^ 2)
      = (Polynomial.expand F 2 (evenSlice f)).eval x := by rw [expand_eval]
    _ = (f + f.comp (-X)).eval x := by rw [evenSlice, key]
    _ = f.eval x + f.eval (-x) := by
        rw [eval_add, eval_comp]
        simp

theorem eval_oddSlice (f : F[X]) (x : F) :
    x * (oddSlice f).eval (x ^ 2) = f.eval x - f.eval (-x) := by
  set h : F[X] := f - f.comp (-X) with hh
  have heven : ∀ n, ¬ 2 ∣ n → (Polynomial.divX h).coeff n = 0 := by
    intro n hn
    rw [coeff_divX, hh, coeff_sub, coeff_comp_neg_X]
    have hsucc : Even (n + 1) := Nat.even_add_one.mpr (by
      intro he
      exact hn (even_iff_two_dvd.mp he))
    rw [hsucc.neg_one_pow]
    ring
  have h0 : h.coeff 0 = 0 := by
    rw [hh, coeff_sub, coeff_comp_neg_X]
    ring
  have key := expand_contract_of_even_support heven
  have heval : h.eval x = (Polynomial.divX h).eval x * x := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add h]
    rw [h0, map_zero, add_zero, eval_mul, eval_X]
  calc x * (oddSlice f).eval (x ^ 2)
      = x * (Polynomial.expand F 2 (oddSlice f)).eval x := by rw [expand_eval]
    _ = x * (Polynomial.divX h).eval x := by rw [oddSlice, key]
    _ = h.eval x := by rw [heval]; ring
    _ = f.eval x - f.eval (-x) := by rw [hh, eval_sub, eval_comp]; simp

/-! Part 2: the fold of a polynomial error IS the slice evaluation -/

variable [DecidableEq F]

/-- On a negation-closed domain avoiding 0 (char ≠ 2), the squaring fiber over `x₀²`
is exactly the antipodal pair. -/
theorem fiber_eq_pair {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D)
    {x₀ : F} (hx₀ : x₀ ∈ D) :
    D.filter (fun x => x ^ 2 = x₀ ^ 2) = {x₀, -x₀} := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hxy : x ^ 2 = x₀ ^ 2 := (Finset.mem_filter.mp hx).2
    have hfac : (x - x₀) * (x + x₀) = 0 := by linear_combination hxy
    rcases mul_eq_zero.mp hfac with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by linear_combination h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by linear_combination h)))
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hx₀, rfl⟩
    · rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨hneg x₀ hx₀, by ring⟩

/-- **The even fold of a polynomial error is the even coefficient slice.** -/
theorem foldVal_polyeval {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldVal D (fun x => f.eval x) (x₀ ^ 2) = (evenSlice f).eval (x₀ ^ 2) := by
  have hne : x₀ ≠ -x₀ := by
    intro hcontra
    apply h0
    have h2x : (2 : F) * x₀ = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · rwa [← h]
  rw [foldVal, fiber_eq_pair hneg hx₀, Finset.sum_pair hne, eval_evenSlice]

/-- **The odd fold of a polynomial error is the odd coefficient slice, twisted by `y`.** -/
theorem foldValOdd_polyeval {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldValOdd D (fun x => f.eval x) (x₀ ^ 2) = x₀ ^ 2 * (oddSlice f).eval (x₀ ^ 2) := by
  have hne : x₀ ≠ -x₀ := by
    intro hcontra
    apply h0
    have h2x : (2 : F) * x₀ = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2x with h | h
    · exact absurd h h2
    · rwa [← h]
  rw [foldValOdd, fiber_eq_pair hneg hx₀, Finset.sum_pair hne]
  have hodd := eval_oddSlice f x₀
  calc f.eval x₀ * x₀ + f.eval (-x₀) * -x₀
      = x₀ * (f.eval x₀ - f.eval (-x₀)) := by ring
    _ = x₀ * (x₀ * (oddSlice f).eval (x₀ ^ 2)) := by rw [hodd]
    _ = x₀ ^ 2 * (oddSlice f).eval (x₀ ^ 2) := by ring

/-- **Branch aliveness = slice nonvanishing** (one level): the even branch is alive at
`y = x₀²` iff the even slice evaluates nonzero there; same for the odd branch (the unit
twist `y ≠ 0` drops out). -/
theorem foldVal_ne_zero_iff {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldVal D (fun x => f.eval x) (x₀ ^ 2) ≠ 0 ↔ (evenSlice f).eval (x₀ ^ 2) ≠ 0 := by
  rw [foldVal_polyeval hneg h0 h2 f hx₀]

theorem foldValOdd_ne_zero_iff {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) {x₀ : F} (hx₀ : x₀ ∈ D) :
    foldValOdd D (fun x => f.eval x) (x₀ ^ 2) ≠ 0 ↔ (oddSlice f).eval (x₀ ^ 2) ≠ 0 := by
  rw [foldValOdd_polyeval hneg h0 h2 f hx₀]
  have hx₀0 : x₀ ≠ 0 := fun h => h0 (h ▸ hx₀)
  constructor
  · intro hne hzero
    exact hne (by rw [hzero, mul_zero])
  · intro hne hzero
    exact hne (by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h) hx₀0
      · exact h)

/-! ## Recomposition, degree bounds, and the per-locus structure theorem

A polynomial is recovered from its slices (`recompose_slices`, char-free `2·f` form),
slices halve degree, vanishing on a point set is locator divisibility (`loc_dvd_iff`),
the live squared locus is bounded by the weight (`weight_ge_live_image`), and putting
everything together: **every error determines a dead locus `Z` with
`|Z| ≥ |D²| − weight`, both slices divisible by `loc Z`, recomposing to `2·f`**
(`low_weight_slice_structure`) — low-weight errors live in the locator-divisible
parameter space of their locus. This is the per-locus (Conjecture-D) counting skeleton:
for fixed `Z` the admissible slice pairs `(he, ho)` range over degree-truncated spaces
of total dimension `deg f − 2·|Z| + O(1)` (`natDegree_evenSlice_le`/`natDegree_oddSlice_le`
supply the budgets), and the open question is the union over loci against the weight
filter. -/

omit [DecidableEq F] in
theorem expand_evenSlice (f : F[X]) :
    Polynomial.expand F 2 (evenSlice f) = f + f.comp (-X) := by
  apply expand_contract_of_even_support
  intro n hn
  rw [coeff_add, coeff_comp_neg_X]
  have hodd' : Odd n := Nat.odd_iff.mpr (by omega)
  rw [hodd'.neg_one_pow]
  ring

omit [DecidableEq F] in
theorem expand_oddSlice (f : F[X]) :
    Polynomial.expand F 2 (oddSlice f) = Polynomial.divX (f - f.comp (-X)) := by
  apply expand_contract_of_even_support
  intro n hn
  rw [coeff_divX, coeff_sub, coeff_comp_neg_X]
  have hsucc : Even (n + 1) := Nat.even_add_one.mpr (fun he => hn (even_iff_two_dvd.mp he))
  rw [hsucc.neg_one_pow]
  ring

omit [DecidableEq F] in
/-- **Char-free recomposition**: a polynomial is recovered (doubled) from its two
coefficient slices. -/
theorem recompose_slices (f : F[X]) :
    Polynomial.expand F 2 (evenSlice f) + X * Polynomial.expand F 2 (oddSlice f) = 2 * f := by
  rw [expand_evenSlice, expand_oddSlice]
  have h0 : (f - f.comp (-X)).coeff 0 = 0 := by
    rw [coeff_sub, coeff_comp_neg_X]; ring
  have hX : Polynomial.divX (f - f.comp (-X)) * X = f - f.comp (-X) := by
    conv_rhs => rw [← Polynomial.divX_mul_X_add (f - f.comp (-X))]
    rw [h0, map_zero, add_zero]
  rw [mul_comm X _, hX]
  ring

omit [DecidableEq F] in
theorem natDegree_contract_two_le (h : F[X]) :
    (Polynomial.contract 2 h).natDegree ≤ h.natDegree / 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Polynomial.coeff_contract (by norm_num : (2:ℕ) ≠ 0)]
  apply coeff_eq_zero_of_natDegree_lt
  omega

omit [DecidableEq F] in
theorem natDegree_evenSlice_le (f : F[X]) :
    (evenSlice f).natDegree ≤ f.natDegree / 2 := by
  refine le_trans (natDegree_contract_two_le _) (Nat.div_le_div_right ?_)
  refine le_trans (natDegree_add_le _ _) (max_le le_rfl ?_)
  calc (f.comp (-X)).natDegree ≤ f.natDegree * (-X : F[X]).natDegree := natDegree_comp_le
    _ ≤ f.natDegree := by
        rw [natDegree_neg, natDegree_X, mul_one]

omit [DecidableEq F] in
theorem natDegree_oddSlice_le (f : F[X]) :
    (oddSlice f).natDegree ≤ f.natDegree / 2 := by
  refine le_trans (natDegree_contract_two_le _) (Nat.div_le_div_right ?_)
  calc (Polynomial.divX (f - f.comp (-X))).natDegree
      ≤ (f - f.comp (-X)).natDegree := natDegree_divX_le
    _ ≤ max f.natDegree (f.comp (-X)).natDegree := natDegree_sub_le _ _
    _ ≤ f.natDegree := max_le le_rfl (by
        calc (f.comp (-X)).natDegree ≤ f.natDegree * (-X : F[X]).natDegree := natDegree_comp_le
          _ ≤ f.natDegree := by rw [natDegree_neg, natDegree_X, mul_one])

set_option linter.unusedSectionVars false in
/-- Vanishing on a finite point set is exactly divisibility by its locator. -/
theorem loc_dvd_iff (Z : Finset F) (p : F[X]) :
    TopLine.loc Z ∣ p ↔ ∀ z ∈ Z, p.eval z = 0 := by
  induction Z using Finset.induction_on with
  | empty =>
    simp [TopLine.loc]
  | @insert a Z ha ih =>
    rw [TopLine.loc, Finset.prod_insert ha]
    constructor
    · rintro ⟨q, rfl⟩ z hz
      rw [eval_mul, eval_mul]
      rcases Finset.mem_insert.mp hz with rfl | hzZ
      · simp
      · rw [eval_prod, Finset.prod_eq_zero hzZ (by simp : eval z ((X : F[X]) - C z) = 0)]
        ring
    · intro hz
      have hA : (X - C a) ∣ p := dvd_iff_isRoot.mpr (hz a (Finset.mem_insert_self a Z))
      have hZ : (∏ b ∈ Z, (X - C b)) ∣ p := by
        rw [← TopLine.loc]
        exact ih.mpr fun z hzZ => hz z (Finset.mem_insert_of_mem hzZ)
      refine IsCoprime.mul_dvd ?_ hA hZ
      refine IsCoprime.prod_right fun z hzZ => ?_
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      have : a ≠ z := fun h => ha (h ▸ hzZ)
      exact (sub_ne_zero.mpr this).isUnit

variable [DecidableEq F]

set_option linter.unusedSectionVars false in
/-- A nonzero fold value at `y` forces a nonzero error value somewhere in the fiber. -/
theorem exists_ne_zero_of_foldVal_ne_zero {D : Finset F} {v : F → F} {y : F}
    (h : foldVal D v y ≠ 0) : ∃ x ∈ D, x ^ 2 = y ∧ v x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact h (Finset.sum_eq_zero fun x hx =>
    hall x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)

set_option linter.unusedSectionVars false in
theorem exists_ne_zero_of_foldValOdd_ne_zero {D : Finset F} {v : F → F} {y : F}
    (h : foldValOdd D v y ≠ 0) : ∃ x ∈ D, x ^ 2 = y ∧ v x ≠ 0 := by
  by_contra hall
  push Not at hall
  refine h (Finset.sum_eq_zero fun x hx => ?_)
  rw [hall x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2, zero_mul]

set_option linter.unusedSectionVars false in
/-- **The weight–dead-locus tradeoff (level 1)**: the number of squared points where some
slice survives is at most the evaluation weight. -/
theorem weight_ge_live_image {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D)
    (h2 : (2 : F) ≠ 0) (f : F[X]) :
    ((D.image (· ^ 2)).filter
        (fun y => (evenSlice f).eval y ≠ 0 ∨ (oddSlice f).eval y ≠ 0)).card
      ≤ (D.filter (fun x => f.eval x ≠ 0)).card := by
  calc ((D.image (· ^ 2)).filter
        (fun y => (evenSlice f).eval y ≠ 0 ∨ (oddSlice f).eval y ≠ 0)).card
      ≤ ((D.filter (fun x => f.eval x ≠ 0)).image (· ^ 2)).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨hyim, hlive⟩ := Finset.mem_filter.mp hy
        obtain ⟨x₀, hx₀D, rfl⟩ := Finset.mem_image.mp hyim
        have hex : ∃ x ∈ D, x ^ 2 = x₀ ^ 2 ∧ f.eval x ≠ 0 := by
          rcases hlive with he | ho
          · exact exists_ne_zero_of_foldVal_ne_zero
              ((foldVal_ne_zero_iff hneg h0 h2 f hx₀D).mpr he)
          · exact exists_ne_zero_of_foldValOdd_ne_zero
              ((foldValOdd_ne_zero_iff hneg h0 h2 f hx₀D).mpr ho)
        obtain ⟨x, hxD, hxy, hfx⟩ := hex
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxD, hfx⟩, hxy⟩
    _ ≤ (D.filter (fun x => f.eval x ≠ 0)).card := Finset.card_image_le

set_option linter.unusedSectionVars false in
/-- **The per-locus structure theorem (level 1) — the Conjecture-D counting skeleton.**
Every polynomial error determines a dead locus `Z` of size at least
`|D^2| − weight`, both its slices are divisible by the locator of `Z`, and the
(locator-divisible) slices recompose to `2·f`. So every low-weight error lives in the
locator-divisible parameter space of its locus. -/
theorem low_weight_slice_structure {D : Finset F} (hneg : ∀ x ∈ D, -x ∈ D)
    (h0 : (0 : F) ∉ D) (h2 : (2 : F) ≠ 0) (f : F[X]) :
    ∃ Z : Finset F, ∃ he ho : F[X],
      Z ⊆ D.image (· ^ 2) ∧
      (D.image (· ^ 2)).card ≤ Z.card + (D.filter (fun x => f.eval x ≠ 0)).card ∧
      evenSlice f = TopLine.loc Z * he ∧
      oddSlice f = TopLine.loc Z * ho ∧
      Polynomial.expand F 2 (TopLine.loc Z * he) +
        X * Polynomial.expand F 2 (TopLine.loc Z * ho) = 2 * f := by
  set Z : Finset F := (D.image (· ^ 2)).filter
    (fun y => (evenSlice f).eval y = 0 ∧ (oddSlice f).eval y = 0) with hZ
  have hZsub : Z ⊆ D.image (· ^ 2) := Finset.filter_subset _ _
  have hcardsplit : Z.card + ((D.image (· ^ 2)).filter
      (fun y => ¬ ((evenSlice f).eval y = 0 ∧ (oddSlice f).eval y = 0))).card
      = (D.image (· ^ 2)).card :=
    Finset.card_filter_add_card_filter_not
      (s := D.image (· ^ 2))
      (p := fun y => (evenSlice f).eval y = 0 ∧ (oddSlice f).eval y = 0)
  have hlive_eq : ((D.image (· ^ 2)).filter
      (fun y => ¬ ((evenSlice f).eval y = 0 ∧ (oddSlice f).eval y = 0))).card
      = ((D.image (· ^ 2)).filter
      (fun y => (evenSlice f).eval y ≠ 0 ∨ (oddSlice f).eval y ≠ 0)).card := by
    congr 1
    apply Finset.filter_congr
    intro y _
    tauto
  have hlive := weight_ge_live_image hneg h0 h2 f
  obtain ⟨he, hhe⟩ := (loc_dvd_iff Z (evenSlice f)).mpr
    (fun z hz => (Finset.mem_filter.mp hz).2.1)
  obtain ⟨ho, hho⟩ := (loc_dvd_iff Z (oddSlice f)).mpr
    (fun z hz => (Finset.mem_filter.mp hz).2.2)
  refine ⟨Z, he, ho, hZsub, ?_, hhe, hho, ?_⟩
  · omega
  · rw [← hhe, ← hho]
    exact recompose_slices f

end LamLeungTwoPow
