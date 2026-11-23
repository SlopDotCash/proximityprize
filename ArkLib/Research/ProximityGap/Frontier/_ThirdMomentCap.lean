/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._IncidenceTripleMass
import ArkLib.Research.ProximityGap.Frontier._PairUnionMomentMean

/-!
# The third-moment cap from a line structure

The reciprocal-locator argument needs one inequality about the agreement
degrees on a restricted coordinate set:

    sum_x f_x^3 <= k m^3 + C L m^2,

where `m` heads are restricted to `L` coordinates, any three distinct
non-collinear heads share at most `k` agreements, and at most eleven heads lie
on any line. This module derives it from that line structure instead of
assuming it.

The derivation is a single ordered-triple census. A triple `(i, j, l)` either
repeats an index, or is distinct and collinear, or is distinct and
non-collinear. Repeats are charged to three coordinate equalities, at most
`3 m^2` in total. Distinct collinear triples are at most `9 m (m - 1)` because
the two endpoints occupy two of the eleven line slots. Only distinct
non-collinear triples may contribute `k`, and there are at most `m^3` of them.

`third_moment_cap` states the result with the constant `12`, which is what
`_CompletionCountThirdMoment` consumes.
-/

set_option autoImplicit false

namespace ProximityGap.ThirdMomentCap

open scoped BigOperators

variable {I X : Type} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- The agreement degree as a filtered cardinality. -/
theorem degree_eq_card_filter (T : I → Finset X) (x : X) :
    ProximityGap.PairUnionMoment.degree T x =
      ((Finset.univ.filter (fun i => x ∈ T i)).card : ℤ) := by
  rw [ProximityGap.PairUnionMoment.degree]
  have h : ((Finset.univ.filter (fun i => x ∈ T i)).card : ℤ) =
      ∑ i, (if x ∈ T i then (1 : ℤ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ T i <;> simp [hx]
  rw [h]

/-- The ordered triple agreement mass is the third moment of the degrees. -/
theorem triple_mass_eq_degree_cube (T : I → Finset X) :
    (∑ i, ∑ j, ∑ l, ((T i ∩ T j ∩ T l).card : ℤ)) =
      ∑ x, (ProximityGap.PairUnionMoment.degree T x) ^ 3 := by
  have h := ProximityGap.IncidenceTripleMass.sum_card_triple_inter_eq_sum_degree_cube T
  have h' : ((∑ i, ∑ j, ∑ l, (T i ∩ T j ∩ T l).card : ℕ) : ℤ) =
      ∑ x, (((Finset.univ.filter (fun i => x ∈ T i)).card : ℕ) : ℤ) ^ 3 := by
    exact_mod_cast h
  have hcast : (∑ i, ∑ j, ∑ l, ((T i ∩ T j ∩ T l).card : ℤ)) =
      ((∑ i, ∑ j, ∑ l, (T i ∩ T j ∩ T l).card : ℕ) : ℤ) := by
    simp only [Nat.cast_sum]
  rw [hcast, h']
  apply Finset.sum_congr rfl
  intro x _
  rw [degree_eq_card_filter]

/-- A single indicator sum over the index type. -/
theorem sum_ite_eq_const (a : I) (c : ℤ) :
    (∑ j : I, (if a = j then c else 0)) = c := by
  have hf : (Finset.univ.filter (fun j : I => a = j)) = {a} := by
    ext j
    simp [eq_comm]
  rw [← Finset.sum_filter, hf, Finset.sum_singleton]

/-- An indicator sum is the cardinality of its filter. -/
theorem sum_ite_one_eq_card (p : I → Prop) [DecidablePred p] :
    (∑ l : I, (if p l then (1 : ℤ) else 0)) =
      ((Finset.univ.filter p).card : ℤ) := by
  rw [← Finset.sum_filter]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The bad-triple indicator is charged to three coordinate equalities and the
distinct collinear indicator. -/
theorem bad_indicator_le (ln : I → I → Finset I) (i j l : I) :
    (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1) ≤
      (if i = j then (1 : ℤ) else 0) + (if j = l then (1 : ℤ) else 0) +
        (if i = l then (1 : ℤ) else 0) +
        (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0) := by
  by_cases hij : i = j <;> by_cases hjl : j = l <;> by_cases hil : i = l <;>
    by_cases hmem : l ∈ ln i j <;> simp [hij, hjl, hil, hmem]

/-- The first coordinate equality summed over the triple product. -/
theorem sum_sum_sum_eq_left (c : ℤ) :
    (∑ i : I, ∑ j : I, ∑ l : I, (if i = j then c else 0)) =
      (Fintype.card I : ℤ) ^ 2 * c := by
  have hconst : ∀ i j : I, (∑ l : I, (if i = j then c else 0)) =
      (Fintype.card I : ℤ) * (if i = j then c else 0) := by
    intro i j
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmid : ∀ i : I, (∑ j : I, ∑ l : I, (if i = j then c else 0)) =
      (Fintype.card I : ℤ) * c := by
    intro i
    simp only [hconst]
    rw [← Finset.mul_sum, sum_ite_eq_const i c]
  simp only [hmid]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The second coordinate equality summed over the triple product. -/
theorem sum_sum_sum_eq_mid (c : ℤ) :
    (∑ _i : I, ∑ j : I, ∑ l : I, (if j = l then c else 0)) =
      (Fintype.card I : ℤ) ^ 2 * c := by
  have hinner : ∀ j : I, (∑ l : I, (if j = l then c else 0)) = c :=
    fun j => sum_ite_eq_const j c
  have hmid : ∀ _i : I, (∑ j : I, ∑ l : I, (if j = l then c else 0)) =
      (Fintype.card I : ℤ) * c := by
    intro _
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [hmid]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The third coordinate equality summed over the triple product. -/
theorem sum_sum_sum_eq_right (c : ℤ) :
    (∑ i : I, ∑ _j : I, ∑ l : I, (if i = l then c else 0)) =
      (Fintype.card I : ℤ) ^ 2 * c := by
  have hinner : ∀ i _j : I, (∑ l : I, (if i = l then c else 0)) = c :=
    fun i _ => sum_ite_eq_const i c
  have hmid : ∀ i : I, (∑ _j : I, ∑ l : I, (if i = l then c else 0)) =
      (Fintype.card I : ℤ) * c := by
    intro i
    simp only [hinner i]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [hmid]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Distinct collinear ordered triples are bounded by nine per ordered pair. -/
theorem collinear_distinct_le (ln : I → I → Finset I)
    (hrefl : ∀ i j, i ≠ j → i ∈ ln i j ∧ j ∈ ln i j)
    (hline : ∀ i j, i ≠ j → (ln i j).card ≤ 11) :
    (∑ i : I, ∑ j : I, ∑ l : I,
        (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0)) ≤
      9 * (Fintype.card I : ℤ) ^ 2 := by
  have hpair : ∀ i j : I, (∑ l : I,
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0)) ≤
      (if i = j then (0 : ℤ) else 9) := by
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij]
      have hzero : ∀ l : I,
          (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0) = 0 := by
        intro l
        rw [if_neg]
        intro h
        exact h.1 hij
      simp only [hzero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      norm_num
    · rw [if_neg hij, sum_ite_one_eq_card]
      have himem : i ∈ ln i j := (hrefl i j hij).1
      have hjmem : j ∈ (ln i j).erase i := by
        rw [Finset.mem_erase]
        exact ⟨Ne.symm hij, (hrefl i j hij).2⟩
      have hcard : (((ln i j).erase i).erase j).card = (ln i j).card - 2 := by
        rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem himem]
        omega
      have hsub : (Finset.univ.filter (fun l : I => i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j)) ⊆
          ((ln i j).erase i).erase j := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        obtain ⟨-, hjl, hil, hmem⟩ := hl
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨Ne.symm hjl, Ne.symm hil, hmem⟩
      have h1 : ((Finset.univ.filter
            (fun l : I => i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j)).card : ℤ) ≤
          ((((ln i j).erase i).erase j).card : ℤ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((((ln i j).erase i).erase j).card : ℤ) ≤ 9 := by
        have h11 := hline i j hij
        omega
      linarith
  have hstep : ∀ i : I, (∑ j : I, ∑ l : I,
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0)) ≤
      9 * ((Fintype.card I : ℤ) - 1) := by
    intro i
    refine (Finset.sum_le_sum (fun j _ => hpair i j)).trans (le_of_eq ?_)
    have hpw : ∀ j : I, (if i = j then (0 : ℤ) else 9) =
        9 - (if i = j then (9 : ℤ) else 0) := by
      intro j
      by_cases h : i = j <;> simp [h]
    simp only [hpw, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_ite_eq_const i 9]
    ring
  refine (Finset.sum_le_sum (fun i _ => hstep i)).trans ?_
  have hconst : (∑ _i : I, 9 * ((Fintype.card I : ℤ) - 1)) =
      9 * (Fintype.card I : ℤ) * ((Fintype.card I : ℤ) - 1) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hconst]
  have hm : (0 : ℤ) ≤ (Fintype.card I : ℤ) := by positivity
  nlinarith

/-- At most `12 m^2` ordered triples repeat an index or are distinct collinear. -/
theorem bad_count_le (ln : I → I → Finset I)
    (hrefl : ∀ i j, i ≠ j → i ∈ ln i j ∧ j ∈ ln i j)
    (hline : ∀ i j, i ≠ j → (ln i j).card ≤ 11) :
    (∑ i : I, ∑ j : I, ∑ l : I,
        (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) ≤
      12 * (Fintype.card I : ℤ) ^ 2 := by
  have hpoint : ∀ i j l : I,
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1) ≤
        (if i = j then (1 : ℤ) else 0) + (if j = l then (1 : ℤ) else 0) +
          (if i = l then (1 : ℤ) else 0) +
          (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0) :=
    bad_indicator_le ln
  have hA := sum_sum_sum_eq_left (1 : ℤ)
  have hB := sum_sum_sum_eq_mid (1 : ℤ)
  have hC := sum_sum_sum_eq_right (1 : ℤ)
  have hD := collinear_distinct_le ln hrefl hline
  have hsplit : (∑ i : I, ∑ j : I, ∑ l : I,
      ((if i = j then (1 : ℤ) else 0) + (if j = l then (1 : ℤ) else 0) +
        (if i = l then (1 : ℤ) else 0) +
        (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0))) =
      (∑ i : I, ∑ j : I, ∑ l : I, (if i = j then (1 : ℤ) else 0)) +
        (∑ i : I, ∑ j : I, ∑ l : I, (if j = l then (1 : ℤ) else 0)) +
        (∑ i : I, ∑ j : I, ∑ l : I, (if i = l then (1 : ℤ) else 0)) +
        (∑ i : I, ∑ j : I, ∑ l : I,
          (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∈ ln i j then (1 : ℤ) else 0)) := by
    simp only [Finset.sum_add_distrib]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Finset.sum_le_sum (fun l _ => hpoint i j l)))).trans ?_
  rw [hsplit, hA, hB, hC]
  have hm : (0 : ℤ) ≤ (Fintype.card I : ℤ) := by positivity
  nlinarith [hD]

/-- The third-moment cap: the line structure forces it with constant `12`. -/
theorem third_moment_cap (T : I → Finset X) (ln : I → I → Finset I) (k : ℕ)
    (hkL : k ≤ Fintype.card X)
    (hrefl : ∀ i j, i ≠ j → i ∈ ln i j ∧ j ∈ ln i j)
    (hline : ∀ i j, i ≠ j → (ln i j).card ≤ 11)
    (hnoncol : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → l ∉ ln i j →
      (T i ∩ T j ∩ T l).card ≤ k) :
    ∑ x, (ProximityGap.PairUnionMoment.degree T x) ^ 3 ≤
      (k : ℤ) * (Fintype.card I : ℤ) ^ 3 +
        12 * (Fintype.card X : ℤ) * (Fintype.card I : ℤ) ^ 2 := by
  have hpoint : ∀ i j l : I, ((T i ∩ T j ∩ T l).card : ℤ) ≤
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (k : ℤ) else (Fintype.card X : ℤ)) := by
    intro i j l
    by_cases hg : i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j
    · rw [if_pos hg]
      exact_mod_cast hnoncol i j l hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
    · rw [if_neg hg]
      exact_mod_cast Finset.card_le_univ (T i ∩ T j ∩ T l)
  have hlift : ∀ i j l : I,
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (k : ℤ) else (Fintype.card X : ℤ)) =
        (k : ℤ) * (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (1 : ℤ) else 0) +
          (Fintype.card X : ℤ) *
            (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1) := by
    intro i j l
    by_cases hg : i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j <;> simp [hg]
  have hgood : (∑ i : I, ∑ j : I, ∑ l : I,
      (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (1 : ℤ) else 0)) +
      (∑ i : I, ∑ j : I, ∑ l : I,
        (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) =
      (Fintype.card I : ℤ) ^ 3 := by
    rw [← Finset.sum_add_distrib]
    have hone : (∑ i : I, ∑ j : I, ∑ l : I, ((1 : ℤ))) = (Fintype.card I : ℤ) ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    calc (∑ i : I, ∑ j : I, ∑ l : I,
          ((if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (1 : ℤ) else 0) +
            (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)))
        = ∑ i : I, ∑ j : I, ∑ l : I, ((1 : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro l _
          by_cases hg : i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j <;> simp [hg]
      _ = _ := hone
  have hB := bad_count_le ln hrefl hline
  have hk : (k : ℤ) ≤ (Fintype.card X : ℤ) := by exact_mod_cast hkL
  have hm : (0 : ℤ) ≤ (Fintype.card I : ℤ) := by positivity
  have hLX : (0 : ℤ) ≤ (Fintype.card X : ℤ) := by positivity
  rw [← triple_mass_eq_degree_cube]
  calc (∑ i : I, ∑ j : I, ∑ l : I, ((T i ∩ T j ∩ T l).card : ℤ))
      ≤ ∑ i : I, ∑ j : I, ∑ l : I,
          (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (k : ℤ) else (Fintype.card X : ℤ)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
          (fun j _ => Finset.sum_le_sum (fun l _ => hpoint i j l)))
    _ = ∑ i : I, ∑ j : I, ∑ l : I,
          ((k : ℤ) * (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (1 : ℤ) else 0) +
            (Fintype.card X : ℤ) *
              (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun l _ => hlift i j l)))
    _ = (k : ℤ) * (∑ i : I, ∑ j : I, ∑ l : I,
          (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (1 : ℤ) else 0)) +
          (Fintype.card X : ℤ) * (∑ i : I, ∑ j : I, ∑ l : I,
            (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (k : ℤ) * (Fintype.card I : ℤ) ^ 3 +
          ((Fintype.card X : ℤ) - (k : ℤ)) * (∑ i : I, ∑ j : I, ∑ l : I,
            (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) := by
        have hsub : ((Fintype.card X : ℤ) - (k : ℤ)) *
            (∑ i : I, ∑ j : I, ∑ l : I,
              (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) =
            (Fintype.card X : ℤ) * (∑ i : I, ∑ j : I, ∑ l : I,
              (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) -
              (k : ℤ) * (∑ i : I, ∑ j : I, ∑ l : I,
                (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) := by
          ring
        rw [hsub]
        have := hgood
        ring
    _ ≤ (k : ℤ) * (Fintype.card I : ℤ) ^ 3 +
          (Fintype.card X : ℤ) * (12 * (Fintype.card I : ℤ) ^ 2) := by
        have hnn : (0 : ℤ) ≤ ∑ i : I, ∑ j : I, ∑ l : I,
            (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1) := by
          apply Finset.sum_nonneg
          intro i _
          apply Finset.sum_nonneg
          intro j _
          apply Finset.sum_nonneg
          intro l _
          by_cases hg : i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j <;> simp [hg]
        have h1 : ((Fintype.card X : ℤ) - (k : ℤ)) *
            (∑ i : I, ∑ j : I, ∑ l : I,
              (if i ≠ j ∧ j ≠ l ∧ i ≠ l ∧ l ∉ ln i j then (0 : ℤ) else 1)) ≤
            (Fintype.card X : ℤ) * (12 * (Fintype.card I : ℤ) ^ 2) := by
          have hle : ((Fintype.card X : ℤ) - (k : ℤ)) ≤ (Fintype.card X : ℤ) := by linarith
          exact mul_le_mul hle hB hnn hLX
        linarith
    _ = (k : ℤ) * (Fintype.card I : ℤ) ^ 3 +
          12 * (Fintype.card X : ℤ) * (Fintype.card I : ℤ) ^ 2 := by
        ring

end ProximityGap.ThirdMomentCap

#print axioms ProximityGap.ThirdMomentCap.degree_eq_card_filter
#print axioms ProximityGap.ThirdMomentCap.triple_mass_eq_degree_cube
#print axioms ProximityGap.ThirdMomentCap.sum_ite_eq_const
#print axioms ProximityGap.ThirdMomentCap.sum_ite_one_eq_card
#print axioms ProximityGap.ThirdMomentCap.bad_indicator_le
#print axioms ProximityGap.ThirdMomentCap.sum_sum_sum_eq_left
#print axioms ProximityGap.ThirdMomentCap.sum_sum_sum_eq_mid
#print axioms ProximityGap.ThirdMomentCap.sum_sum_sum_eq_right
#print axioms ProximityGap.ThirdMomentCap.collinear_distinct_le
#print axioms ProximityGap.ThirdMomentCap.bad_count_le
#print axioms ProximityGap.ThirdMomentCap.third_moment_cap
