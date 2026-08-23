/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroSharpNewtonBase

/-!
# Char-0 W3-anti, rung 2: discharging the `r = 2` instance of `SharpNewtonBessel` (#444)

`CharZeroSharpNewtonBase.lean` discharged the `r = 1` base of the named input `SharpNewtonBessel d`
(lane B2's char-0 W3-anti reduction). This file extends the discharge to the **second rung**,
`r = 2`, which is `3·c_1·c_3 ≤ 2·c_2²` for `c_r = besselCoeff d r`.

We supply the next closed form

  **`besselCoeff_three : besselCoeff d 3 = d·(6d² − 9d + 4)/36`**

by the three-way partition of `antidiagonalTuple d 3`:
* `d`        "triple" tuples (one coord `= 3`, term `1/(3!)² = 1/36`);
* `d·(d−1)`  "two-one" tuples (one coord `= 2`, one coord `= 1`, term `1/(2!)²·1/(1!)² = 1/4`);
* `C(d,3)`   "split" tuples (three coords `= 1`, term `1`),
so `c_3 = d/36 + d(d−1)/4 + C(d,3) = d(6d² − 9d + 4)/36`.

Combined with `besselCoeff_one (= d)` and `besselCoeff_two (= d(2d−1)/4)`, the `r = 2` sharp-Newton
step `3·d·c_3 ≤ 2·c_2²` clears to `6d ≥ 5` (true for `d ≥ 1`, strict slack).

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `besselCoeff_three` — `besselCoeff d 3 = d·(6d² − 9d + 4)/36`.
* `sharpNewton_two` — `3 · besselCoeff d 1 · besselCoeff d 3 ≤ 2 · (besselCoeff d 2)²`.
* `Rstep_two_le_Rstep_one` — `Rstep d 2 ≤ Rstep d 1`, via B2's `R_antitone_iff_sharpNewton`.

## Honesty / scope

Discharges the **`r = 2`** instance (char-0 only) of `SharpNewtonBessel`, extending the base file's
`r = 1`. Does NOT close `SharpNewtonBessel d` in general, does NOT touch the char-`p` transfer (lane
B3, proven NOT char-`p`-robust), raises NOTHING on the open CORE ceiling.
-/

open Finset BigOperators

set_option linter.style.longLine false

namespace ProximityGap.PrizeWorkbench

variable {d : ℕ}

/-- The `besselCoeff` summand at tuple `m`. -/
private def bterm3 (m : Fin d → ℕ) : ℚ := ∏ i, (1 : ℚ) / (Nat.factorial (m i))^2

/-- Each coordinate of a tuple summing to `3` is `≤ 3`. -/
private lemma coord_le_three {m : Fin d → ℕ} (hm : ∑ i, m i = 3) (i : Fin d) : m i ≤ 3 := by
  calc m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 3 := hm

/-- The two-coordinate mass bound: for any `i ≠ j`, `m i + m j ≤ ∑ m`. -/
private lemma pair_le {m : Fin d → ℕ} {i j : Fin d} (hj : i ≠ j) : m i + m j ≤ ∑ k, m k := by
  have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  calc m i + m j = ∑ k ∈ ({i, j} : Finset (Fin d)), m k := by rw [Finset.sum_pair hj]
    _ ≤ ∑ k, m k := Finset.sum_le_sum_of_subset hsub

/-- Classify a tuple summing to `3` by its maximal coordinate: `3` (triple), `2` (two-one), or
`≤ 1` (split). -/
private lemma three_trichotomy {m : Fin d → ℕ} (hm : ∑ i, m i = 3) :
    (∃ i, m i = 3) ∨ (∃ i, m i = 2) ∨ (∀ k, m k ≤ 1) := by
  by_cases h3 : ∃ i, m i = 3
  · exact Or.inl h3
  · by_cases h2 : ∃ i, m i = 2
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ?_)
      intro k
      have hk3 := coord_le_three hm k
      simp only [not_exists] at h3 h2
      have := h3 k; have := h2 k; omega

/-- On a "triple" tuple (`m i = 3`, others `0`), the summand is `1/36`. -/
private lemma bterm3_triple {m : Fin d → ℕ} (hm : ∑ i, m i = 3) {i : Fin d} (hi : m i = 3) :
    bterm3 m = 1 / 36 := by
  have hzero : ∀ j, j ≠ i → m j = 0 := by
    intro j hj
    by_contra hjne
    have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr hjne
    have := pair_le (m := m) (i := i) (j := j) (Ne.symm hj)
    rw [hm, hi] at this; omega
  unfold bterm3
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have herase : ∀ j ∈ Finset.univ.erase i, (1 : ℚ) / (Nat.factorial (m j))^2 = 1 := by
    intro j hj; rw [Finset.mem_erase] at hj; rw [hzero j hj.1]; norm_num
  rw [Finset.prod_congr rfl herase, Finset.prod_const_one, one_mul, hi]
  norm_num [Nat.factorial]

/-- On a "split" tuple (all coords `≤ 1`), the summand is `1`. -/
private lemma bterm3_split {m : Fin d → ℕ} (hall : ∀ k, m k ≤ 1) : bterm3 m = 1 := by
  unfold bterm3
  apply Finset.prod_eq_one
  intro j _
  have : m j = 0 ∨ m j = 1 := by have := hall j; omega
  rcases this with h | h <;> rw [h] <;> norm_num

/-- The "two-one" tuple from an ordered distinct pair `(i, j)`: `i ↦ 2`, `j ↦ 1`, rest `0`. -/
private def twoOne (i j : Fin d) : Fin d → ℕ := fun k => if k = i then 2 else if k = j then 1 else 0

/-- A two-one tuple sums to `3`. -/
private lemma twoOne_sum {i j : Fin d} (hij : i ≠ j) : ∑ k, twoOne i j k = 3 := by
  unfold twoOne
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), if_pos rfl]
  have h2 : ∑ k ∈ Finset.univ.erase i, (if k = i then 2 else if k = j then 1 else 0)
      = ∑ k ∈ Finset.univ.erase i, (if k = j then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_erase] at hk; rw [if_neg hk.1]
  rw [h2, Finset.sum_ite_eq' (Finset.univ.erase i) j (fun _ => (1 : ℕ))]
  rw [if_pos (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]

/-- On a two-one tuple, the summand is `1/(2!)² · 1/(1!)² = 1/4`. -/
private lemma bterm3_twoOne (i j : Fin d) : bterm3 (twoOne i j) = 1 / 4 := by
  unfold bterm3 twoOne
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl]
  have herase : ∀ k ∈ Finset.univ.erase i,
      (1 : ℚ) / (Nat.factorial (if k = i then 2 else if k = j then 1 else 0))^2 = 1 := by
    intro k hk; rw [Finset.mem_erase] at hk; rw [if_neg hk.1]
    by_cases hkj : k = j <;> simp [hkj]
  rw [Finset.prod_congr rfl herase, Finset.prod_const_one, one_mul]
  norm_num [Nat.factorial]

/-- A tuple summing to `3` with some coord `= 2` is the two-one tuple of the unique ordered pair
`(i, j)` with `m i = 2`, `m j = 1` (`i ≠ j`). -/
private lemma eq_twoOne_of {m : Fin d → ℕ} (hm : ∑ k, m k = 3)
    {i : Fin d} (hi : m i = 2) : ∃ j, i ≠ j ∧ m = twoOne i j := by
  classical
  have hother_le : ∀ k, k ≠ i → m k ≤ 1 := by
    intro k hk
    have hpair := pair_le (m := m) (i := i) (j := k) (Ne.symm hk)
    rw [hm, hi] at hpair; omega
  have hsumoff : ∑ k ∈ Finset.univ.erase i, m k = 1 := by
    have he : (∑ k ∈ Finset.univ.erase i, m k) + m i = ∑ k, m k :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    rw [hm, hi] at he; omega
  have hsupp : ((Finset.univ.erase i).filter (fun k => m k = 1)).card = 1 := by
    have hcardeq : ((Finset.univ.erase i).filter (fun k => m k = 1)).card
        = ∑ k ∈ Finset.univ.erase i, m k := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k hk
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hother_le k (Finset.mem_erase.mp hk).1) with
        h0 | h1
      · simp [h0]
      · simp [h1]
    rw [hcardeq, hsumoff]
  obtain ⟨j, hjeq⟩ := Finset.card_eq_one.mp hsupp
  have hjmem : j ∈ (Finset.univ.erase i).filter (fun k => m k = 1) := by
    rw [hjeq]; exact Finset.mem_singleton_self j
  rw [Finset.mem_filter, Finset.mem_erase] at hjmem
  have hij : i ≠ j := Ne.symm hjmem.1.1
  have hj1 : m j = 1 := hjmem.2
  have hjuniq : ∀ k ∈ Finset.univ.erase i, k ≠ j → m k = 0 := by
    intro k hk hkj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hother_le k (Finset.mem_erase.mp hk).1) with
      h0 | h1
    · exact h0
    · exfalso
      have hmem : k ∈ (Finset.univ.erase i).filter (fun k => m k = 1) :=
        Finset.mem_filter.mpr ⟨hk, h1⟩
      rw [hjeq, Finset.mem_singleton] at hmem
      exact hkj hmem
  refine ⟨j, hij, ?_⟩
  funext k
  unfold twoOne
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl, hi]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj; rw [if_pos rfl, hj1]
    · rw [if_neg hkj, hjuniq k (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩) hkj]

/-- The two-one tuple has no coord `= 3`. -/
private lemma twoOne_no_three (i j : Fin d) : ¬ ∃ k, twoOne i j k = 3 := by
  rintro ⟨k, hk⟩
  unfold twoOne at hk
  by_cases hki : k = i
  · simp [hki] at hk
  · rw [if_neg hki] at hk
    by_cases hkj : k = j <;> simp [hkj] at hk

/-- The two-one tuple has a coord `= 2` (namely `i`). -/
private lemma twoOne_has_two (i j : Fin d) : ∃ k, twoOne i j k = 2 :=
  ⟨i, by unfold twoOne; rw [if_pos rfl]⟩

/-! ### The three sub-sums of `besselCoeff d 3`. -/

/-- **Triple sum.** Tuples summing to `3` with some coord `= 3` are `Pi.single i 3` (bij `Fin d`);
each summand `1/36`. -/
private lemma sum_triple :
    ∑ m ∈ (Finset.Nat.antidiagonalTuple d 3).filter (fun m => ∃ i, m i = 3), bterm3 m
      = (d : ℚ) * (1 / 36) := by
  classical
  have himg : (Finset.Nat.antidiagonalTuple d 3).filter (fun m => ∃ i, m i = 3)
      = Finset.univ.image (fun i : Fin d => (Pi.single i 3 : Fin d → ℕ)) := by
    ext m
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, i, hi⟩
      refine ⟨i, ?_⟩
      have hzero : ∀ j, j ≠ i → m j = 0 := by
        intro j hj
        by_contra hjne
        have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr hjne
        have := pair_le (m := m) (i := i) (j := j) (Ne.symm hj)
        rw [hm, hi] at this; omega
      funext j
      by_cases hji : j = i
      · subst hji; rw [hi, Pi.single_eq_same]
      · rw [hzero j hji, Pi.single_eq_of_ne hji]
    · rintro ⟨i, rfl⟩
      refine ⟨?_, i, Pi.single_eq_same i 3⟩
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ i) h
  rw [himg, Finset.sum_image (by
    intro i _ j _ hij
    by_contra hne
    have h := congrFun hij i
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h
    exact absurd h (by decide))]
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      bterm3 (Pi.single i 3 : Fin d → ℕ) = 1 / 36 := by
    intro i _
    refine bterm3_triple ?_ (Pi.single_eq_same i 3)
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **Two-one sum.** Tuples summing to `3` with no coord `= 3` but some coord `= 2` are the two-one
tuples (bij `univ.offDiag`, card `d(d-1)`); each summand `1/4`. -/
private lemma sum_twoOne :
    ∑ m ∈ (Finset.Nat.antidiagonalTuple d 3).filter
        (fun m => ¬ (∃ i, m i = 3) ∧ (∃ i, m i = 2)), bterm3 m
      = (d : ℚ) * ((d : ℚ) - 1) / 4 := by
  classical
  have himg : (Finset.Nat.antidiagonalTuple d 3).filter
      (fun m => ¬ (∃ i, m i = 3) ∧ (∃ i, m i = 2))
      = (Finset.univ.offDiag).image (fun p : Fin d × Fin d => twoOne p.1 p.2) := by
    ext m
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Finset.mem_image,
      Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hm, _h3, i, hi⟩
      obtain ⟨j, hij, hmeq⟩ := eq_twoOne_of hm hi
      exact ⟨(i, j), hij, hmeq.symm⟩
    · rintro ⟨⟨i, j⟩, hij, rfl⟩
      exact ⟨twoOne_sum hij, twoOne_no_three i j, twoOne_has_two i j⟩
  have hinj : ∀ p ∈ (Finset.univ : Finset (Fin d)).offDiag,
      ∀ q ∈ (Finset.univ : Finset (Fin d)).offDiag,
      twoOne p.1 p.2 = twoOne q.1 q.2 → p = q := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    have hpij : i ≠ j := (Finset.mem_offDiag.mp hp).2.2
    simp only at heq
    have hii : i = i' := by
      by_contra hne
      have hc := congrFun heq i
      simp only [twoOne] at hc
      split_ifs at hc with h1 h2 <;> first | exact hne h1 | exact absurd hc (by decide)
    subst hii
    have hjj : j = j' := by
      by_contra hne
      have hc := congrFun heq j
      simp only [twoOne, if_neg (Ne.symm hpij)] at hc
      rw [if_neg hne] at hc
      exact absurd hc (by decide)
    subst hjj; rfl
  -- each summand is 1/4, so the sum is (1/4)·card; card = card offDiag = d(d-1).
  have hterm : ∀ m ∈ (Finset.Nat.antidiagonalTuple d 3).filter
      (fun m => ¬ (∃ i, m i = 3) ∧ (∃ i, m i = 2)), bterm3 m = 1 / 4 := by
    intro m hm
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm
    obtain ⟨i, hi⟩ := hm.2.2
    obtain ⟨j, _hij, hmeq⟩ := eq_twoOne_of hm.1 hi
    rw [hmeq]
    exact bterm3_twoOne i j
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- card of the filtered set = card offDiag = d(d-1)
  have hcard : ((Finset.Nat.antidiagonalTuple d 3).filter
      (fun m => ¬ (∃ i, m i = 3) ∧ (∃ i, m i = 2))).card
      = (Finset.univ : Finset (Fin d)).offDiag.card := by
    rw [himg, Finset.card_image_of_injOn (fun p hp q hq h => hinj p hp q hq h)]
  rw [hcard, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hle : d ≤ d * d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left d h
  have hcast : ((d * d - d : ℕ) : ℚ) = (d : ℚ) * (d : ℚ) - (d : ℚ) := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [hcast]; ring

/-- **Split sum.** Tuples summing to `3` with all coords `≤ 1` (no coord `= 3` and no coord `= 2`)
are the three-element supports (bij `powersetCard 3 univ`, card `C(d,3)`); each summand `1`. -/
private lemma sum_split :
    ∑ m ∈ (Finset.Nat.antidiagonalTuple d 3).filter
        (fun m => ¬ (∃ i, m i = 3) ∧ ¬ (∃ i, m i = 2)), bterm3 m
      = ((d.choose 3 : ℕ) : ℚ) := by
  classical
  have hall_iff : ∀ {m : Fin d → ℕ}, ∑ i, m i = 3 →
      ((¬ (∃ i, m i = 3) ∧ ¬ (∃ i, m i = 2)) ↔ ∀ k, m k ≤ 1) := by
    intro m hm
    constructor
    · rintro ⟨h3, h2⟩ k
      have hk3 := coord_le_three hm k
      simp only [not_exists] at h3 h2
      have := h3 k; have := h2 k; omega
    · intro hall
      refine ⟨?_, ?_⟩
      · rintro ⟨i, hi⟩; have := hall i; omega
      · rintro ⟨i, hi⟩; have := hall i; omega
  have hterm : ∀ m ∈ (Finset.Nat.antidiagonalTuple d 3).filter
      (fun m => ¬ (∃ i, m i = 3) ∧ ¬ (∃ i, m i = 2)), bterm3 m = 1 := by
    intro m hm
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm
    exact bterm3_split ((hall_iff hm.1).mp hm.2)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have hcard : ((Finset.Nat.antidiagonalTuple d 3).filter
      (fun m => ¬ (∃ i, m i = 3) ∧ ¬ (∃ i, m i = 2))).card
      = ((Finset.univ : Finset (Fin d)).powersetCard 3).card := by
    apply Finset.card_bij (fun m _ => Finset.univ.filter (fun k => m k = 1))
    · intro m hm
      rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm
      have hall := (hall_iff hm.1).mp hm.2
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have hcardeq : (Finset.univ.filter (fun k => m k = 1)).card = ∑ k, m k := by
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro k _
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hall k) with h0 | h1
        · simp [h0]
        · simp [h1]
      rw [hcardeq, hm.1]
    · intro m hm n hn hmn
      rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hm hn
      have hallm := (hall_iff hm.1).mp hm.2
      have halln := (hall_iff hn.1).mp hn.2
      funext k
      have hk : (k ∈ Finset.univ.filter (fun k => m k = 1))
          ↔ (k ∈ Finset.univ.filter (fun k => n k = 1)) := by rw [hmn]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hallm k) with h0 | h1
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (halln k) with h0' | h1'
        · rw [h0, h0']
        · exact absurd (hk.mpr h1') (by rw [h0]; decide)
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (halln k) with h0' | h1'
        · exact absurd (hk.mp h1) (by rw [h0']; decide)
        · rw [h1, h1']
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      refine ⟨fun k => if k ∈ s then 1 else 0, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
        have hsum : ∑ k, (if k ∈ s then 1 else 0) = 3 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul,
            mul_one, hs.2]
        refine ⟨hsum, ?_, ?_⟩
        · rintro ⟨i, hi⟩; by_cases hmem : i ∈ s <;> simp [hmem] at hi
        · rintro ⟨i, hi⟩; by_cases hmem : i ∈ s <;> simp [hmem] at hi
      · ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hmem : k ∈ s <;> simp [hmem]
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ### Assembly: the closed form and the `r = 2` sharp-Newton inequality. -/

/-- **The closed form** `besselCoeff d 3 = d·(6d² − 9d + 4)/36`. -/
theorem besselCoeff_three (d : ℕ) :
    besselCoeff d 3 = (d : ℚ) * (6 * d ^ 2 - 9 * d + 4) / 36 := by
  classical
  have hsum : besselCoeff d 3 = ∑ m ∈ Finset.Nat.antidiagonalTuple d 3, bterm3 m := rfl
  -- split off the triple part, then split the rest into two-one and split.
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not
      (Finset.Nat.antidiagonalTuple d 3) (fun m => ∃ i, m i = 3) bterm3, sum_triple]
  -- the "not triple" part splits by "has a 2"
  rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.Nat.antidiagonalTuple d 3).filter (fun m => ¬ ∃ i, m i = 3))
      (fun m => ∃ i, m i = 2) bterm3]
  -- rewrite the two nested filters into the conjunction forms used by sum_twoOne / sum_split
  have e1 : ((Finset.Nat.antidiagonalTuple d 3).filter (fun m => ¬ ∃ i, m i = 3)).filter
        (fun m => ∃ i, m i = 2)
      = (Finset.Nat.antidiagonalTuple d 3).filter
        (fun m => ¬ (∃ i, m i = 3) ∧ (∃ i, m i = 2)) := by
    rw [Finset.filter_filter]
  have e2 : ((Finset.Nat.antidiagonalTuple d 3).filter (fun m => ¬ ∃ i, m i = 3)).filter
        (fun m => ¬ ∃ i, m i = 2)
      = (Finset.Nat.antidiagonalTuple d 3).filter
        (fun m => ¬ (∃ i, m i = 3) ∧ ¬ (∃ i, m i = 2)) := by
    rw [Finset.filter_filter]
  rw [e1, e2, sum_twoOne, sum_split]
  -- 6·C(d,3) = d.descFactorial 3 = d·(d-1)·(d-2)  (over ℕ), so cast cleanly.
  have hdesc : d.descFactorial 3 = Nat.factorial 3 * d.choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose d 3
  have hdescval : (d.descFactorial 3 : ℚ) = (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) := by
    rcases d with _ | _ | d'
    · simp [Nat.descFactorial]
    · simp [Nat.descFactorial]
    · simp only [Nat.descFactorial, Nat.succ_sub_one]
      push_cast
      ring
  have hchoose : ((d.choose 3 : ℕ) : ℚ) = (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 6 := by
    have h6 : ((Nat.factorial 3 : ℕ) : ℚ) = 6 := by norm_num [Nat.factorial]
    have : ((d.descFactorial 3 : ℕ) : ℚ) = 6 * (d.choose 3 : ℚ) := by
      rw [hdesc]; push_cast [h6]; ring
    rw [hdescval] at this
    linarith [this]
  rw [hchoose]
  ring

/-- **The `r = 2` instance of `SharpNewtonBessel`**: `3·c_1·c_3 ≤ 2·c_2²`. With `c_1 = d`,
`c_2 = d(2d−1)/4`, `c_3 = d(6d²−9d+4)/36`, this clears to `6d ≥ 5` (true for `d ≥ 1`). -/
theorem sharpNewton_two (d : ℕ) :
    3 * besselCoeff d 1 * besselCoeff d 3 ≤ 2 * (besselCoeff d 2) ^ 2 := by
  rw [besselCoeff_one, besselCoeff_two, besselCoeff_three]
  rcases d with _ | d'
  · simp
  · have hx : (0 : ℚ) ≤ (d' : ℚ) := Nat.cast_nonneg d'
    have hgap : 2 * (((d':ℚ)+1) * (2*((d':ℚ)+1) - 1) / 4) ^ 2
        - 3 * ((d':ℚ)+1) * (((d':ℚ)+1) * (6*((d':ℚ)+1)^2 - 9*((d':ℚ)+1) + 4) / 36)
        = ((d':ℚ)+1)^2 * (6*((d':ℚ)+1) - 5) / 24 := by ring
    have hpos : (0:ℚ) ≤ ((d':ℚ)+1)^2 * (6*((d':ℚ)+1) - 5) / 24 := by
      have : (0:ℚ) ≤ 6*((d':ℚ)+1) - 5 := by nlinarith [hx]
      positivity
    push_cast
    nlinarith [hgap, hpos]

/-- **Second-step descent (char-0 W3-anti, rung 2).** `Rstep d 2 ≤ Rstep d 1`, via B2's
`R_antitone_iff_sharpNewton` at `r = 1`. -/
theorem Rstep_two_le_Rstep_one {d : ℕ} (hd : 1 ≤ d) : Rstep d 2 ≤ Rstep d 1 := by
  rw [R_antitone_iff_sharpNewton hd 1]
  -- goal: (1+2)·c_3·c_1 ≤ (1+1)·c_2²   i.e.   3·c_3·c_1 ≤ 2·c_2²
  have h := sharpNewton_two d
  change ((1 + 2 : ℕ) : ℚ) * besselCoeff d (1 + 2) * besselCoeff d 1
      ≤ ((1 + 1 : ℕ) : ℚ) * besselCoeff d (1 + 1) ^ 2
  norm_num
  nlinarith [h]

end ProximityGap.PrizeWorkbench

/-! ## Axiom audit -/
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_three
#print axioms ProximityGap.PrizeWorkbench.sharpNewton_two
#print axioms ProximityGap.PrizeWorkbench.Rstep_two_le_Rstep_one
