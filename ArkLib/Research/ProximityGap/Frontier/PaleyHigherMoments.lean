/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.HyperellipticStepanov
import Mathlib.Algebra.Order.Chebyshev

/-!
# Unconditional all-order even moments of shifted quadratic character sums

Using the general-degree elementary Stepanov–Weil bound from `HyperellipticStepanov.lean`,
this file proves completely unconditionally (standard Lean axioms only, zero external Weil
axioms):

* `card_allEven_tuples_le`: the number of `2r`-tuples in `T^(2r)` in which every value appears
  with even multiplicity is at most `(2r - 1)!! · |T|^r`.
* `shifted_even_moment_le`: for EVERY finite field `F` of odd characteristic, EVERY `r ≥ 1`,
  and EVERY `T : Finset F`,
  `∑ x : F, W_T(x)^(2r) ≤ (2r - 1)!! · |T|^r · |F| + 9 r · |T|^(2r) · √|F|`.
* `shifted_sixth_moment_ultra`: for every odd-characteristic finite field with `|F| ≥ 10^7 + 1`
  and every `T : Finset F`,
  `∑ x : F, W_T(x)^6 ≤ 15 |T|^3 |F| + 135 |T|^5 √|F| + (111/10) |T|^6 √|F|`.
* `sum_sq_charSum_tuples_le`: the squared-sum version
  `∑ a ∈ T^(2r), (∑ x : F, ∏ i, χ(x - a i))^2 ≤ (2r - 1)!! · |T|^r · |F|^2 + 81 r^2 · |T|^(2r) · |F|`
  that directly powers the all-order inverted-chart Gram moment theorem.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleyHigherMoments

open Finset ProximityGap.HyperellipticStepanov

/-! ## 1. Double factorial and even-multiplicity tuple counting -/

/-- Odd double factorial `(2r - 1)!!`: `doubleFact 0 = 1`, `doubleFact (r + 1) = (2r + 1) * doubleFact r`. -/
def doubleFact : ℕ → ℕ
  | 0 => 1
  | r + 1 => (2 * r + 1) * doubleFact r

theorem doubleFact_zero : doubleFact 0 = 1 := rfl
theorem doubleFact_one : doubleFact 1 = 1 := rfl
theorem doubleFact_two : doubleFact 2 = 3 := rfl
theorem doubleFact_three : doubleFact 3 = 15 := rfl

/-- A tuple has all-even multiplicities if every entry appears an even number of times. -/
def IsAllEvenTuple {α : Type*} [DecidableEq α] {n : ℕ} (a : Fin n → α) : Prop :=
  ∀ u : α, Even (Finset.univ.filter fun i : Fin n => a i = u).card

instance instDecidablePredIsAllEvenTuple {α : Type*} [DecidableEq α] {n : ℕ} (a : Fin n → α) :
    Decidable (IsAllEvenTuple a) := by
  have hiff : IsAllEvenTuple a ↔
      ∀ i : Fin n, Even (Finset.univ.filter fun j : Fin n => a j = a i).card := by
    constructor
    · intro h i; exact h (a i)
    · intro h u
      by_cases hu : ∃ i : Fin n, a i = u
      · obtain ⟨i, rfl⟩ := hu; exact h i
      · push Not at hu
        have hemp : (Finset.univ.filter fun j : Fin n => a j = u) = ∅ := by
          ext j; simp [hu j]
        rw [hemp, Finset.card_empty]
        exact ⟨0, rfl⟩
  exact decidable_of_iff' _ hiff

/-- Finite set of all `n`-tuples with entries in `T`. -/
def tupleSet {α : Type*} [DecidableEq α] (T : Finset α) (n : ℕ) : Finset (Fin n → α) :=
  Fintype.piFinset fun _ : Fin n => T

theorem card_tupleSet {α : Type*} [DecidableEq α] (T : Finset α) (n : ℕ) :
    (tupleSet T n).card = T.card ^ n := by
  simp [tupleSet, Fintype.card_piFinset]

theorem mem_tupleSet {α : Type*} [DecidableEq α] {T : Finset α} {n : ℕ} {a : Fin n → α} :
    a ∈ tupleSet T n ↔ ∀ i, a i ∈ T := by
  simp [tupleSet, Fintype.mem_piFinset]

private theorem card_filter_cons_insertNth {α : Type*} [DecidableEq α] {m : ℕ}
    (v : α) (j : Fin (m + 1)) (b : Fin m → α) (u : α) :
    (Finset.univ.filter fun i : Fin (m + 2) =>
        (Fin.cons v (Fin.insertNth j v b : Fin (m + 1) → α) : Fin (m + 2) → α) i = u).card =
      (Finset.univ.filter fun k : Fin m => b k = u).card + if v = u then 2 else 0 := by
  have hcons : ∀ (f : Fin (m + 1) → α),
      (Finset.univ.filter fun i : Fin (m + 2) => (Fin.cons v f : Fin (m + 2) → α) i = u).card =
        (if v = u then 1 else 0) + (Finset.univ.filter fun i : Fin (m + 1) => f i = u).card := by
    intro f
    have hsum : ∀ {k : ℕ} (g : Fin k → α),
        (Finset.univ.filter fun i : Fin k => g i = u).card =
          ∑ i : Fin k, if g i = u then 1 else 0 := fun g => by
      rw [← Finset.sum_filter]; simp
    rw [hsum, hsum, Fin.sum_univ_succ]
    simp
  have hins : (Finset.univ.filter fun i : Fin (m + 1) =>
        (Fin.insertNth j v b : Fin (m + 1) → α) i = u).card =
      (if v = u then 1 else 0) + (Finset.univ.filter fun k : Fin m => b k = u).card := by
    have hsum : ∀ {k : ℕ} (g : Fin k → α),
        (Finset.univ.filter fun i : Fin k => g i = u).card =
          ∑ i : Fin k, if g i = u then 1 else 0 := fun g => by
      rw [← Finset.sum_filter]; simp
    rw [hsum, hsum, Fin.sum_univ_succAbove _ j]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [hcons, hins]
  split_ifs <;> omega

/-- **Pairing count**: at most `(2r - 1)!! · |T|^r` tuples in `T^(2r)` have every value occurring
with even multiplicity. -/
theorem card_allEven_tuples_le {α : Type*} [DecidableEq α] (T : Finset α) (r : ℕ) :
    ((tupleSet T (2 * r)).filter IsAllEvenTuple).card ≤ doubleFact r * T.card ^ r := by
  induction r with
  | zero =>
    rw [doubleFact_zero, pow_zero, mul_one]
    have hle := Finset.card_le_card (Finset.filter_subset IsAllEvenTuple (tupleSet T 0))
    simpa [card_tupleSet] using hle
  | succ r ih =>
    let S := (tupleSet T (2 * (r + 1))).filter IsAllEvenTuple
    let P := T ×ˢ ((Finset.univ : Finset (Fin (2 * r + 1))) ×ˢ
      ((tupleSet T (2 * r)).filter IsAllEvenTuple))
    let φ : α × Fin (2 * r + 1) × (Fin (2 * r) → α) → (Fin (2 * (r + 1)) → α) :=
      fun ⟨v, j, b⟩ => Fin.cons v (Fin.insertNth j v b)
    have hsub : S ⊆ P.image φ := by
      intro a ha
      rw [Finset.mem_filter, mem_tupleSet] at ha
      obtain ⟨haT, haEven⟩ := ha
      -- `a 0` has even multiplicity `≥ 1`, hence `≥ 2`, so it recurs at some `j.succ`.
      have h0mem : (0 : Fin (2 * (r + 1))) ∈ Finset.univ.filter (fun i => a i = a 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hcard_pos : 1 ≤ (Finset.univ.filter fun i => a i = a 0).card :=
        Finset.card_pos.mpr ⟨0, h0mem⟩
      have hcard_ge2 : 2 ≤ (Finset.univ.filter fun i => a i = a 0).card := by
        obtain ⟨k, hk⟩ := haEven (a 0)
        omega
      have hex : ∃ i : Fin (2 * (r + 1)), i ≠ 0 ∧ a i = a 0 := by
        have hlt : 1 < (Finset.univ.filter fun i => a i = a 0).card := by omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
        rw [Finset.mem_filter] at hx hy
        by_cases hx0 : x = 0
        · exact ⟨y, fun hy0 => hxy (hx0.trans hy0.symm), hy.2⟩
        · exact ⟨x, hx0, hx.2⟩
      obtain ⟨i, hi0, hai⟩ := hex
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi0
      let b : Fin (2 * r) → α := fun k => a (j.succAbove k).succ
      have hrec : φ (a 0, j, b) = a := by
        funext x
        refine Fin.cases ?_ ?_ x
        · simp [φ]
        · intro y
          simp only [φ, Fin.cons_succ]
          refine Fin.succAboveCases j ?_ ?_ y
          · simp [Fin.insertNth_apply_same, hai]
          · intro k
            simp [Fin.insertNth_apply_succAbove, b]
      have hbT : b ∈ tupleSet T (2 * r) := mem_tupleSet.mpr fun k => haT _
      have hbEven : IsAllEvenTuple b := by
        intro u
        have hcnt := card_filter_cons_insertNth (a 0) j b u
        have hrec' : (Fin.cons (a 0) (Fin.insertNth j (a 0) b : Fin (2 * r + 1) → α) :
            Fin (2 * r + 2) → α) = a := hrec
        rw [hrec'] at hcnt
        change (Finset.univ.filter fun i : Fin (2 * (r + 1)) => a i = u).card =
          (Finset.univ.filter fun k : Fin (2 * r) => b k = u).card +
            if a 0 = u then 2 else 0 at hcnt
        obtain ⟨c, hc⟩ := haEven u
        rw [hc] at hcnt
        split_ifs at hcnt with hvu
        · exact ⟨c - 1, by omega⟩
        · exact ⟨c, by omega⟩
      exact Finset.mem_image.mpr
        ⟨(a 0, j, b), Finset.mem_product.mpr ⟨haT 0, Finset.mem_product.mpr
          ⟨Finset.mem_univ j, Finset.mem_filter.mpr ⟨hbT, hbEven⟩⟩⟩, hrec⟩
    calc S.card ≤ (P.image φ).card := Finset.card_le_card hsub
      _ ≤ P.card := Finset.card_image_le
      _ = T.card * ((2 * r + 1) * ((tupleSet T (2 * r)).filter IsAllEvenTuple).card) := by
          simp [P, Finset.card_product]
      _ ≤ T.card * ((2 * r + 1) * (doubleFact r * T.card ^ r)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
      _ = doubleFact (r + 1) * T.card ^ (r + 1) := by
          rw [doubleFact, pow_succ]; ring

/-! ## 2. Expansion of `2r`-th moments into tuple character sums -/

section Moments

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Shifted quadratic character sum `W_T(x) = ∑ t ∈ T, χ(x - t)`. -/
def shiftedCharSum (T : Finset F) (x : F) : ℤ :=
  ∑ t ∈ T, quadraticChar F (x - t)

/-- Complete character sum associated to a tuple `a : Fin n → F`. -/
def tupleCharSum {n : ℕ} (a : Fin n → F) : ℤ :=
  ∑ x : F, ∏ i : Fin n, quadraticChar F (x - a i)

/-- Expanding `(∑ t ∈ T, f t) ^ n` as a sum over `tupleSet T n`. -/
theorem pow_sum_eq_sum_tupleSet {α R : Type*} [DecidableEq α] [CommSemiring R]
    (T : Finset α) (n : ℕ) (f : α → R) :
    (∑ t ∈ T, f t) ^ n = ∑ a ∈ tupleSet T n, ∏ i : Fin n, f (a i) := by
  classical
  calc (∑ t ∈ T, f t) ^ n
      = ∏ _i : Fin n, ∑ t : T, f t.1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          simp only [Finset.univ_eq_attach, Finset.sum_attach]
    _ = ∑ a : Fin n → T, ∏ i : Fin n, f (a i).1 := Fintype.prod_sum (fun _ (t : T) => f t.1)
    _ = ∑ a ∈ tupleSet T n, ∏ i : Fin n, f (a i) := by
          refine Finset.sum_bij (fun (a : Fin n → T) _ i => (a i).1) ?_ ?_ ?_ ?_
          · intro a _; exact mem_tupleSet.mpr fun i => (a i).2
          · intro a₁ _ a₂ _ h; funext i; exact Subtype.ext (congrFun h i)
          · intro b hb; exact ⟨fun i => ⟨b i, mem_tupleSet.mp hb i⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl

theorem shiftedCharSum_pow_eq (T : Finset F) (n : ℕ) (x : F) :
    (shiftedCharSum T x) ^ n =
      ∑ a ∈ tupleSet T n, ∏ i : Fin n, quadraticChar F (x - a i) :=
  pow_sum_eq_sum_tupleSet T n fun t => quadraticChar F (x - t)

theorem sum_shiftedCharSum_pow_eq (T : Finset F) (n : ℕ) :
    ∑ x : F, (shiftedCharSum T x) ^ n = ∑ a ∈ tupleSet T n, tupleCharSum a := by
  simp_rw [shiftedCharSum_pow_eq, tupleCharSum]
  exact Finset.sum_comm

private theorem tupleCharSum_abs_le_card {n : ℕ} (a : Fin n → F) :
    |tupleCharSum a| ≤ (Fintype.card F : ℤ) := by
  calc |tupleCharSum a|
      ≤ ∑ x : F, |∏ i : Fin n, quadraticChar F (x - a i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : F, (1 : ℤ) := Finset.sum_le_sum fun x _ => by
        rw [Finset.abs_prod]
        have hle : ∀ (s : Finset (Fin n)), ∏ i ∈ s, |quadraticChar F (x - a i)| ≤ 1 := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | @insert u s hu ih =>
            rw [Finset.prod_insert hu]
            have hu1 : |quadraticChar F (x - a u)| ≤ 1 := by
              rcases (quadraticChar_isQuadratic F) (x - a u) with h | h | h <;> rw [h] <;> decide
            have hs0 : 0 ≤ ∏ v ∈ s, |quadraticChar F (x - a v)| :=
              Finset.prod_nonneg fun _ _ => abs_nonneg _
            nlinarith
        exact hle Finset.univ
    _ = Fintype.card F := by simp

private theorem oddSet_nonempty_of_not_allEven {n : ℕ} {a : Fin n → F}
    (hna : ¬ IsAllEvenTuple a) :
    ((Finset.univ.image a).filter fun u =>
      Odd (Finset.univ.filter fun i : Fin n => a i = u).card).Nonempty := by
  unfold IsAllEvenTuple at hna
  push Not at hna
  obtain ⟨u, hu⟩ := hna
  have hodd : Odd (Finset.univ.filter fun i : Fin n => a i = u).card :=
    Nat.not_even_iff_odd.mp hu
  have hpos : 0 < (Finset.univ.filter fun i : Fin n => a i = u).card := by
    rcases hodd with ⟨k, hk⟩; omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hui : u ∈ Finset.univ.image a :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  exact ⟨u, Finset.mem_filter.mpr ⟨hui, hodd⟩⟩

private theorem oddSet_and_evenSet_card_bounds {r : ℕ} (a : Fin (2 * r) → F) :
    let supp := Finset.univ.image a
    let oddSet := supp.filter fun u => Odd (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card
    let evenSet := supp.filter fun u => Even (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card
    oddSet.card ≤ 2 * r ∧ evenSet.card ≤ r ∧ Even oddSet.card := by
  classical
  intro supp oddSet evenSet
  have hsum_card : ∑ u ∈ supp, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card = 2 * r := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := supp) (f := a)
      (fun i _ => Finset.mem_image_of_mem a (Finset.mem_univ i))
    simpa [Finset.card_univ, Fintype.card_fin] using this.symm
  have hodd_le : oddSet.card ≤ 2 * r := by
    calc oddSet.card ≤ supp.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Finset.univ : Finset (Fin (2 * r))).card := Finset.card_image_le
      _ = 2 * r := by simp
  have heven_ge2 : ∀ u ∈ evenSet, 2 ≤ (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu.1
    have hpos : 1 ≤ (Finset.univ.filter fun j : Fin (2 * r) => a j = a i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    obtain ⟨k, hk⟩ := hu.2
    omega
  have heven_le : evenSet.card ≤ r := by
    have h2 : 2 * evenSet.card ≤ 2 * r := by
      calc 2 * evenSet.card
          = ∑ _u ∈ evenSet, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ u ∈ evenSet, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card :=
            Finset.sum_le_sum heven_ge2
        _ ≤ ∑ u ∈ supp, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 2 * r := hsum_card
    omega
  have hodd_even : Even oddSet.card := by
    have hsplit : supp = oddSet ∪ evenSet := by
      ext u
      simp only [oddSet, evenSet, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hu
        rcases Nat.even_or_odd (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card with h | h
        · exact Or.inr ⟨hu, h⟩
        · exact Or.inl ⟨hu, h⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    have hdisj : Disjoint oddSet evenSet := by
      rw [Finset.disjoint_left]
      intro u huo hue
      exact (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hue).2) (Finset.mem_filter.mp huo).2
    rw [hsplit, Finset.sum_union hdisj] at hsum_card
    have hE : Even (∑ u ∈ evenSet, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card) :=
      Finset.even_sum _ fun u hu => (Finset.mem_filter.mp hu).2
    have hO : Even (∑ u ∈ oddSet, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card) := by
      have htot : Even (2 * r) := even_two_mul r
      rw [← hsum_card] at htot
      exact (Nat.even_add.mp htot).mpr hE
    have hmod : (∑ u ∈ oddSet, (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card) % 2 =
        oddSet.card % 2 := by
      have hsum_mod : ∀ (s : Finset F) (g : F → ℕ), (∀ u ∈ s, g u % 2 = 1) →
          (∑ u ∈ s, g u) % 2 = s.card % 2 := by
        intro s g hg
        induction s using Finset.induction_on with
        | empty => simp
        | @insert x s hx ih =>
          rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx, Nat.add_mod,
            hg x (Finset.mem_insert_self x s), ih (fun u hu => hg u (Finset.mem_insert_of_mem hu))]
          omega
      exact hsum_mod oddSet _ fun u hu => Nat.odd_iff.mp (Finset.mem_filter.mp hu).2
    rw [Nat.even_iff] at hO ⊢
    omega
  exact ⟨hodd_le, heven_le, hodd_even⟩

/-- For any non-all-even `2r`-tuple, `|tupleCharSum a| ≤ 9 * r * √|F|`. -/
theorem tupleCharSum_notAllEven_le (hF : ringChar F ≠ 2) {r : ℕ} (_hr : 1 ≤ r)
    {a : Fin (2 * r) → F} (hna : ¬ IsAllEvenTuple a) :
    |(tupleCharSum a : ℝ)| ≤ (9 * r : ℝ) * Real.sqrt (Fintype.card F) := by
  have hne := oddSet_nonempty_of_not_allEven hna
  have hraw := tuple_charSum_abs_le hF a hne
  obtain ⟨hodd_le, heven_le, _⟩ := oddSet_and_evenSet_card_bounds a
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    have : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
    simpa using Real.sqrt_le_sqrt this
  have ho' : ((Finset.univ.image a |>.filter fun u =>
      Odd (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card).card : ℝ) ≤ 2 * r := by
    exact_mod_cast hodd_le
  have he' : ((Finset.univ.image a |>.filter fun u =>
      Even (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card).card : ℝ) ≤ r := by
    exact_mod_cast heven_le
  calc |(tupleCharSum a : ℝ)|
      ≤ (4 * ((Finset.univ.image a |>.filter fun u =>
          Odd (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card).card : ℝ)) *
          Real.sqrt (Fintype.card F) +
        ((Finset.univ.image a |>.filter fun u =>
          Even (Finset.univ.filter fun i : Fin (2 * r) => a i = u).card).card : ℝ) := hraw
    _ ≤ (4 * (2 * r : ℝ)) * Real.sqrt (Fintype.card F) + (r : ℝ) * Real.sqrt (Fintype.card F) := by
        nlinarith [Real.sqrt_nonneg (Fintype.card F), Nat.cast_nonneg (α := ℝ) r]
    _ = (9 * r : ℝ) * Real.sqrt (Fintype.card F) := by ring

/-- **Unconditional all-order `2r`-th moment of shifted quadratic character sums**:
for EVERY finite field `F` of odd characteristic, EVERY `r ≥ 1`, and EVERY `T : Finset F`,
`∑ x : F, W_T(x)^(2r) ≤ (2r - 1)!! · |T|^r · |F| + 9 r · |T|^(2r) · √|F|`. -/
theorem shifted_even_moment_le (hF : ringChar F ≠ 2) (T : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    ((∑ x : F, (shiftedCharSum T x) ^ (2 * r) : ℤ) : ℝ) ≤
      (doubleFact r : ℝ) * (T.card : ℝ) ^ r * Fintype.card F +
        (9 * r : ℝ) * (T.card : ℝ) ^ (2 * r) * Real.sqrt (Fintype.card F) := by
  classical
  rw [sum_shiftedCharSum_pow_eq]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not (tupleSet T (2 * r)) IsAllEvenTuple]
  apply add_le_add
  · -- All-even tuples
    calc ∑ a ∈ (tupleSet T (2 * r)).filter IsAllEvenTuple, (tupleCharSum a : ℝ)
        ≤ ∑ _a ∈ (tupleSet T (2 * r)).filter IsAllEvenTuple, (Fintype.card F : ℝ) :=
          Finset.sum_le_sum fun a _ => by
            have h := (abs_le.mp (tupleCharSum_abs_le_card a)).2
            exact_mod_cast h
      _ = (((tupleSet T (2 * r)).filter IsAllEvenTuple).card : ℝ) * Fintype.card F := by simp
      _ ≤ ((doubleFact r * T.card ^ r : ℕ) : ℝ) * Fintype.card F :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_allEven_tuples_le T r)
            (Nat.cast_nonneg _)
      _ = (doubleFact r : ℝ) * (T.card : ℝ) ^ r * Fintype.card F := by push_cast; ring
  · -- Non-all-even tuples
    calc ∑ a ∈ (tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a), (tupleCharSum a : ℝ)
        ≤ ∑ _a ∈ (tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a),
            ((9 * r : ℝ) * Real.sqrt (Fintype.card F)) :=
          Finset.sum_le_sum fun a ha =>
            (le_abs_self _).trans (tupleCharSum_notAllEven_le hF hr (Finset.mem_filter.mp ha).2)
      _ = (((tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a)).card : ℝ) *
            ((9 * r : ℝ) * Real.sqrt (Fintype.card F)) := by simp
      _ ≤ ((tupleSet T (2 * r)).card : ℝ) * ((9 * r : ℝ) * Real.sqrt (Fintype.card F)) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) (by positivity)
      _ = (9 * r : ℝ) * (T.card : ℝ) ^ (2 * r) * Real.sqrt (Fintype.card F) := by
          rw [card_tupleSet]; push_cast; ring

/-- **Squared tuple-sum bound (for the all-order Gram moment)**:
`∑ a ∈ T^(2r), (tupleCharSum a)^2 ≤ (2r - 1)!! · |T|^r · |F|^2 + 81 r^2 · |T|^(2r) · |F|`. -/
theorem sum_sq_tupleCharSum_le (hF : ringChar F ≠ 2) (T : Finset F) {r : ℕ} (hr : 1 ≤ r) :
    ((∑ a ∈ tupleSet T (2 * r), (tupleCharSum a) ^ 2 : ℤ) : ℝ) ≤
      (doubleFact r : ℝ) * (T.card : ℝ) ^ r * (Fintype.card F : ℝ) ^ 2 +
        (81 * (r : ℝ) ^ 2) * (T.card : ℝ) ^ (2 * r) * Fintype.card F := by
  classical
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not (tupleSet T (2 * r)) IsAllEvenTuple]
  apply add_le_add
  · calc ∑ a ∈ (tupleSet T (2 * r)).filter IsAllEvenTuple, (tupleCharSum a : ℝ) ^ 2
        ≤ ∑ _a ∈ (tupleSet T (2 * r)).filter IsAllEvenTuple, (Fintype.card F : ℝ) ^ 2 :=
          Finset.sum_le_sum fun a _ => by
            have h : |(tupleCharSum a : ℝ)| ≤ (Fintype.card F : ℝ) := by
              exact_mod_cast tupleCharSum_abs_le_card a
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (((tupleSet T (2 * r)).filter IsAllEvenTuple).card : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
          simp
      _ ≤ ((doubleFact r * T.card ^ r : ℕ) : ℝ) * (Fintype.card F : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_allEven_tuples_le T r) (sq_nonneg _)
      _ = (doubleFact r : ℝ) * (T.card : ℝ) ^ r * (Fintype.card F : ℝ) ^ 2 := by push_cast; ring
  · calc ∑ a ∈ (tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a), (tupleCharSum a : ℝ) ^ 2
        ≤ ∑ _a ∈ (tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a),
            ((81 * (r : ℝ) ^ 2) * Fintype.card F) :=
          Finset.sum_le_sum fun a ha => by
            have h := tupleCharSum_notAllEven_le hF hr (Finset.mem_filter.mp ha).2
            have hsq : |(tupleCharSum a : ℝ)| ^ 2 ≤ ((9 * r : ℝ) * Real.sqrt (Fintype.card F)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h 2
            rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
            linarith
      _ = (((tupleSet T (2 * r)).filter (fun a => ¬ IsAllEvenTuple a)).card : ℝ) *
            ((81 * (r : ℝ) ^ 2) * Fintype.card F) := by simp
      _ ≤ ((tupleSet T (2 * r)).card : ℝ) * ((81 * (r : ℝ) ^ 2) * Fintype.card F) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) (by positivity)
      _ = (81 * (r : ℝ) ^ 2) * (T.card : ℝ) ^ (2 * r) * Fintype.card F := by
          rw [card_tupleSet]; push_cast; ring

/-! ## 3. Ultra-sharp sixth moment (`r = 3`, `|F| ≥ 10^7 + 1`) -/

private theorem card_nonInjective_six_le {α : Type*} [DecidableEq α] (T : Finset α) :
    ((tupleSet T 6).filter fun a => ¬ Function.Injective a).card ≤ 15 * T.card ^ 5 := by
  classical
  let pairs := (Finset.univ : Finset (Fin 6 × Fin 6)).filter fun p => p.1 < p.2
  have hpairs : pairs.card = 15 := by decide
  have hsub : ((tupleSet T 6).filter fun a => ¬ Function.Injective a) ⊆
      pairs.biUnion fun p => (tupleSet T 6).filter fun a => a p.1 = a p.2 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haT, hni⟩ := ha
    unfold Function.Injective at hni
    push Not at hni
    obtain ⟨i, j, hij, hne⟩ := hni
    rw [Finset.mem_biUnion]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩,
        Finset.mem_filter.mpr ⟨haT, hij⟩⟩
    · exact ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        Finset.mem_filter.mpr ⟨haT, hij.symm⟩⟩
  have hper : ∀ p ∈ pairs,
      ((tupleSet T 6).filter fun a => a p.1 = a p.2).card ≤ T.card ^ 5 := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := ne_of_lt hlt
    -- `p.1` is in the range of `p.2.succAbove` since `p.1 ≠ p.2`.
    obtain ⟨i0, hi0⟩ := Fin.exists_succAbove_eq hne
    let ψ : (Fin 5 → α) → (Fin 6 → α) := fun b => Fin.insertNth p.2 (b i0) b
    have himg : ((tupleSet T 6).filter fun a => a p.1 = a p.2) ⊆ (tupleSet T 5).image ψ := by
      intro a ha
      rw [Finset.mem_filter, mem_tupleSet] at ha
      let b : Fin 5 → α := fun k => a (p.2.succAbove k)
      have hbi0 : b i0 = a p.2 := by simp [b, hi0, ha.2]
      have hrec : ψ b = a := by
        funext x
        refine Fin.succAboveCases p.2 ?_ ?_ x
        · simp [ψ, Fin.insertNth_apply_same, hbi0]
        · intro k
          simp [ψ, Fin.insertNth_apply_succAbove, b]
      exact Finset.mem_image.mpr ⟨b, mem_tupleSet.mpr fun k => ha.1 _, hrec⟩
    calc ((tupleSet T 6).filter fun a => a p.1 = a p.2).card
        ≤ ((tupleSet T 5).image ψ).card := Finset.card_le_card himg
      _ ≤ (tupleSet T 5).card := Finset.card_image_le
      _ = T.card ^ 5 := card_tupleSet T 5
  calc ((tupleSet T 6).filter fun a => ¬ Function.Injective a).card
      ≤ (pairs.biUnion fun p => (tupleSet T 6).filter fun a => a p.1 = a p.2).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, ((tupleSet T 6).filter fun a => a p.1 = a p.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, T.card ^ 5 := Finset.sum_le_sum hper
    _ = 15 * T.card ^ 5 := by simp [hpairs]

private theorem tupleCharSum_six_injective_ultra (hF : ringChar F ≠ 2)
    (hq : 10 ^ 7 + 1 ≤ Fintype.card F) {a : Fin 6 → F} (hinj : Function.Injective a) :
    |(tupleCharSum a : ℝ)| ≤ (111 / 10 : ℝ) * Real.sqrt (Fintype.card F) := by
  classical
  let S := Finset.univ.image a
  have hScard : S.card = 6 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have heq : tupleCharSum a = ∑ x : F, quadraticChar F ((prodLinear S).eval x) := by
    unfold tupleCharSum
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prodLinear_eval, map_prod, Finset.prod_image (fun i _ j _ h => hinj h)]
  rw [heq]
  have hultra := hyperelliptic_stepanov_deg6_ultra hF hq (prodLinear_monic S)
    (prodLinear_squarefree S) (by rw [prodLinear_natDegree, hScard])
  have hsq : ((∑ x : F, quadraticChar F ((prodLinear S).eval x) : ℤ) : ℝ) ^ 2 ≤
      ((111 / 10 : ℝ) * Real.sqrt (Fintype.card F)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have h' : (100 : ℝ) * ((∑ x : F, quadraticChar F ((prodLinear S).eval x) : ℤ) : ℝ) ^ 2 ≤
        12321 * (Fintype.card F : ℝ) := by exact_mod_cast hultra
    linarith
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩

private theorem tupleCharSum_six_nonInj_notAllEven (hF : ringChar F ≠ 2)
    (hq : 683 ≤ Fintype.card F) {a : Fin 6 → F}
    (hna : ¬ IsAllEvenTuple a) (hni : ¬ Function.Injective a) :
    |(tupleCharSum a : ℝ)| ≤ 9 * Real.sqrt (Fintype.card F) := by
  classical
  set supp := Finset.univ.image a
  set oddSet := supp.filter fun u => Odd (Finset.univ.filter fun i : Fin 6 => a i = u).card
  set evenSet := supp.filter fun u => Even (Finset.univ.filter fun i : Fin 6 => a i = u).card
  have hne : oddSet.Nonempty := oddSet_nonempty_of_not_allEven hna
  have hbounds : oddSet.card ≤ 6 ∧ evenSet.card ≤ 3 ∧ Even oddSet.card :=
    oddSet_and_evenSet_card_bounds (r := 3) a
  obtain ⟨hodd_le, heven_le, hodd_even⟩ := hbounds
  have hlt6 : supp.card < 6 := by
    by_contra hge
    have hcard6 : supp.card = (Finset.univ : Finset (Fin 6)).card := by
      have hle : supp.card ≤ 6 := by simpa using Finset.card_image_le (f := a) (s := Finset.univ)
      simp; omega
    have hinj : Function.Injective a := by
      have := Finset.injOn_of_card_image_eq hcard6
      intro i j hij
      exact this (Finset.mem_univ i) (Finset.mem_univ j) hij
    exact hni hinj
  have hodd_lt6 : oddSet.card < 6 :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hlt6
  have hodd_pos : 1 ≤ oddSet.card := Finset.card_pos.mpr hne
  have hcases : oddSet.card = 2 ∨ oddSet.card = 4 := by
    obtain ⟨k, hk⟩ := hodd_even
    omega
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    have : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast (by omega : 1 ≤ Fintype.card F)
    simpa using Real.sqrt_le_sqrt this
  have hq9 : (3 : ℝ) ≤ 9 * Real.sqrt (Fintype.card F) := by linarith
  have hsplit_card : oddSet.card + evenSet.card = supp.card := by
    have hsplit : supp = oddSet ∪ evenSet := by
      ext u
      simp only [oddSet, evenSet, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hu
        rcases Nat.even_or_odd (Finset.univ.filter fun i : Fin 6 => a i = u).card with h | h
        · exact Or.inr ⟨hu, h⟩
        · exact Or.inl ⟨hu, h⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    have hdisj : Disjoint oddSet evenSet := by
      rw [Finset.disjoint_left]
      intro u huo hue
      exact (Nat.not_odd_iff_even.mpr (Finset.mem_filter.mp hue).2) (Finset.mem_filter.mp huo).2
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit]
  rcases hcases with h2 | h4
  · have hb : |tupleCharSum a| ≤ 1 + (evenSet.card : ℤ) := tuple_charSum_oddCard_two hF a h2
    have hb' : |(tupleCharSum a : ℝ)| ≤ 1 + (evenSet.card : ℝ) := by exact_mod_cast hb
    have he3' : (evenSet.card : ℝ) ≤ 3 := by exact_mod_cast heven_le
    linarith
  · have hdiff_int : |tupleCharSum a -
        ∑ x : F, quadraticChar F ((prodLinear oddSet).eval x)| ≤ (evenSet.card : ℤ) :=
      charSum_prod_sub_squarefree_le Finset.univ a
    have hdiff : |(tupleCharSum a : ℝ) -
        ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| ≤ (evenSet.card : ℝ) := by
      exact_mod_cast hdiff_int
    have h4step := hyperelliptic_stepanov_deg4_tight hF hq (prodLinear_monic oddSet)
      (prodLinear_squarefree oddSet) (by rw [prodLinear_natDegree, h4])
    have h4abs : |((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| ≤
        8 * Real.sqrt (Fintype.card F) := by
      have hsq : ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ) ^ 2 ≤
          (8 * Real.sqrt (Fintype.card F)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        have h' : ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ) ^ 2 ≤
            64 * (Fintype.card F : ℝ) := by exact_mod_cast h4step
        linarith
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
    have he1 : evenSet.card ≤ 1 := by omega
    have he1' : (evenSet.card : ℝ) ≤ 1 := by exact_mod_cast he1
    have htri : |(tupleCharSum a : ℝ)| ≤
        |(tupleCharSum a : ℝ) - ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| +
        |((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)| := by
      simpa only [sub_add_cancel] using abs_add_le
        ((tupleCharSum a : ℝ) - ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ))
        ((∑ x : F, quadraticChar F ((prodLinear oddSet).eval x) : ℤ) : ℝ)
    linarith

/-- **Ultra-sharp sixth moment for large odd-characteristic finite fields (`q ≥ 10^7 + 1`)**:
`∑ x : F, W_T(x)^6 ≤ 15 |T|^3 q + 135 |T|^5 √q + (111/10) |T|^6 √q`. -/
theorem shifted_sixth_moment_ultra (hF : ringChar F ≠ 2) (hq : 10 ^ 7 + 1 ≤ Fintype.card F)
    (T : Finset F) :
    ((∑ x : F, (shiftedCharSum T x) ^ 6 : ℤ) : ℝ) ≤
      15 * (T.card : ℝ) ^ 3 * Fintype.card F +
        135 * (T.card : ℝ) ^ 5 * Real.sqrt (Fintype.card F) +
        (111 / 10 : ℝ) * (T.card : ℝ) ^ 6 * Real.sqrt (Fintype.card F) := by
  classical
  rw [sum_shiftedCharSum_pow_eq]
  push_cast
  let A := tupleSet T 6
  rw [← Finset.sum_filter_add_sum_filter_not A IsAllEvenTuple]
  rw [← Finset.sum_filter_add_sum_filter_not (A.filter fun a => ¬ IsAllEvenTuple a)
    (fun a => ¬ Function.Injective a)]
  have h1 : ∑ a ∈ A.filter IsAllEvenTuple, (tupleCharSum a : ℝ) ≤
      15 * (T.card : ℝ) ^ 3 * Fintype.card F := by
    calc ∑ a ∈ A.filter IsAllEvenTuple, (tupleCharSum a : ℝ)
        ≤ ∑ _a ∈ A.filter IsAllEvenTuple, (Fintype.card F : ℝ) :=
          Finset.sum_le_sum fun a _ => by
            have h := (abs_le.mp (tupleCharSum_abs_le_card a)).2
            exact_mod_cast h
      _ = ((A.filter IsAllEvenTuple).card : ℝ) * Fintype.card F := by simp
      _ ≤ ((doubleFact 3 * T.card ^ 3 : ℕ) : ℝ) * Fintype.card F :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_allEven_tuples_le T 3)
            (Nat.cast_nonneg _)
      _ = 15 * (T.card : ℝ) ^ 3 * Fintype.card F := by
          rw [doubleFact_three]; push_cast; ring
  have h2 : ∑ a ∈ (A.filter fun a => ¬ IsAllEvenTuple a).filter (fun a => ¬ Function.Injective a),
        (tupleCharSum a : ℝ) ≤ 135 * (T.card : ℝ) ^ 5 * Real.sqrt (Fintype.card F) := by
    let B := (A.filter fun a => ¬ IsAllEvenTuple a).filter (fun a => ¬ Function.Injective a)
    have hBsub : B ⊆ A.filter (fun a => ¬ Function.Injective a) := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_filter] at ha
      exact Finset.mem_filter.mpr ⟨ha.1.1, ha.2⟩
    calc ∑ a ∈ B, (tupleCharSum a : ℝ)
        ≤ ∑ _a ∈ B, (9 * Real.sqrt (Fintype.card F)) :=
          Finset.sum_le_sum fun a ha => by
            rw [Finset.mem_filter, Finset.mem_filter] at ha
            exact (le_abs_self _).trans (tupleCharSum_six_nonInj_notAllEven hF (by omega) ha.1.2 ha.2)
      _ = (B.card : ℝ) * (9 * Real.sqrt (Fintype.card F)) := by simp
      _ ≤ ((15 * T.card ^ 5 : ℕ) : ℝ) * (9 * Real.sqrt (Fintype.card F)) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_le_card hBsub).trans (card_nonInjective_six_le T))
            (by positivity)
      _ = 135 * (T.card : ℝ) ^ 5 * Real.sqrt (Fintype.card F) := by push_cast; ring
  have h3 : ∑ a ∈ (A.filter fun a => ¬ IsAllEvenTuple a).filter (fun a => ¬ ¬ Function.Injective a),
        (tupleCharSum a : ℝ) ≤ (111 / 10 : ℝ) * (T.card : ℝ) ^ 6 * Real.sqrt (Fintype.card F) := by
    let C := (A.filter fun a => ¬ IsAllEvenTuple a).filter (fun a => ¬ ¬ Function.Injective a)
    have hCsub : C ⊆ A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    calc ∑ a ∈ C, (tupleCharSum a : ℝ)
        ≤ ∑ _a ∈ C, ((111 / 10 : ℝ) * Real.sqrt (Fintype.card F)) :=
          Finset.sum_le_sum fun a ha => by
            have hinj : Function.Injective a := not_not.mp (Finset.mem_filter.mp ha).2
            exact (le_abs_self _).trans (tupleCharSum_six_injective_ultra hF hq hinj)
      _ = (C.card : ℝ) * ((111 / 10 : ℝ) * Real.sqrt (Fintype.card F)) := by simp
      _ ≤ (A.card : ℝ) * ((111 / 10 : ℝ) * Real.sqrt (Fintype.card F)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hCsub) (by positivity)
      _ = (111 / 10 : ℝ) * (T.card : ℝ) ^ 6 * Real.sqrt (Fintype.card F) := by
          rw [show A.card = T.card ^ 6 from card_tupleSet T 6]; push_cast; ring
  linarith

end Moments

end ProximityGap.PaleyHigherMoments

#print axioms ProximityGap.PaleyHigherMoments.card_allEven_tuples_le
#print axioms ProximityGap.PaleyHigherMoments.shifted_even_moment_le
#print axioms ProximityGap.PaleyHigherMoments.sum_sq_tupleCharSum_le
#print axioms ProximityGap.PaleyHigherMoments.shifted_sixth_moment_ultra
