/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Chebyshev

/-!
# Coverage pigeonhole for multi-γ line decoding

A self-contained combinatorial double-counting / averaging bound used by the GG25 multi-γ
overlap-coverage extraction (issue #140): if many agreement sets each cover a large fraction
of the coordinates, some coordinate is covered many times.  This is the "double coverage"
step that forces a joint pair in the repaired ABF26 T4.21 line-decoding argument.

## Main results

* `Coverage.sum_card_eq_sum_degree` — incidence double-counting: `∑ |S i| = ∑ₓ deg x`.
* `Coverage.exists_degree_gt` — averaging pigeonhole: if `k·n < ∑ |S i|` some coordinate has
  degree `> k`.
-/

open Finset

namespace ArkLib.Coverage

/-- **Incidence double-counting.**  For a finite indexed family `S : κ → Finset ι` over a
fintype `ι`, the total size equals the sum over coordinates of the coordinate degree
(number of sets containing it). -/
theorem sum_card_eq_sum_degree {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (S : κ → Finset ι) :
    (∑ i, (S i).card) = ∑ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card := by
  classical
  have hcard : ∀ i, (S i).card = ∑ x : ι, (if x ∈ S i then (1 : ℕ) else 0) := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    ext x; simp
  have hdeg : ∀ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card
      = ∑ i, (if x ∈ S i then (1 : ℕ) else 0) := by
    intro x; rw [Finset.card_filter]
  simp_rw [hcard, hdeg]
  exact Finset.sum_comm

/-- **Coverage pigeonhole.**  If the total agreement mass `∑ |S i|` exceeds `k · |ι|`, some
coordinate lies in strictly more than `k` of the sets — the double-coverage that forces a
joint pair in GG25 multi-γ line decoding (issue #140). -/
theorem exists_degree_gt {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (S : κ → Finset ι) (k : ℕ) (hk : k * Fintype.card ι < ∑ i, (S i).card) :
    ∃ x : ι, k < (Finset.univ.filter (fun i => x ∈ S i)).card := by
  classical
  by_contra h
  push Not at h
  have hsum : (∑ i, (S i).card) ≤ k * Fintype.card ι := by
    rw [sum_card_eq_sum_degree]
    calc (∑ x : ι, (Finset.univ.filter (fun i => x ∈ S i)).card)
        ≤ ∑ _x : ι, k := Finset.sum_le_sum (fun x _ => h x)
      _ = k * Fintype.card ι := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  omega

/-- **Joint-pair mass bound** (Cauchy–Schwarz form of GG25 coverage).  The total ordered
pairwise-intersection mass of the agreement sets is at least `(∑ |S i|)² / |ι|`:
`(∑ i, |S i|)² ≤ |ι| · ∑ i, ∑ j, |S i ∩ S j|`.  Hence when the agreement sets are large their
pairwise overlaps are forced to be large in aggregate — so some pair shares many coordinates,
the joint-pair witness the repaired line-decoding argument extracts (issue #140). -/
theorem sq_sum_card_le_card_mul_sum_inter {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (S : κ → Finset ι) :
    (∑ i, (S i).card) ^ 2 ≤ Fintype.card ι * ∑ i, ∑ j, (S i ∩ S j).card := by
  classical
  set deg : ι → ℕ := fun x => (Finset.univ.filter (fun i => x ∈ S i)).card with hdeg
  have hf : ∀ x : ι, deg x = ∑ i, (if x ∈ S i then (1 : ℕ) else 0) := by
    intro x
    change (Finset.univ.filter (fun i => x ∈ S i)).card
      = ∑ i, (if x ∈ S i then (1 : ℕ) else 0)
    rw [Finset.card_filter]
  have hinter : ∀ i j : κ, (S i ∩ S j).card
      = ∑ x : ι, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0) := by
    intro i j
    calc
      (S i ∩ S j).card
          = (Finset.univ.filter (fun x : ι => x ∈ S i ∩ S j)).card := by
              congr 1
              ext x
              simp
      _ = ∑ x : ι, (if x ∈ S i ∩ S j then (1 : ℕ) else 0) := by
              rw [Finset.card_filter]
      _ = ∑ x : ι, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;>
                simp [hi, hj, Finset.mem_inter]
  have hident : (∑ i, ∑ j, (S i ∩ S j).card) = ∑ x : ι, (deg x) ^ 2 := by
    have step1 : (∑ i, ∑ j, ∑ x : ι, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0))
        = ∑ i, ∑ x : ι, ∑ j, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_comm
    have step2 : (∑ i, ∑ x : ι, ∑ j, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0))
        = ∑ x : ι, ∑ i, ∑ j, (if x ∈ S i then (1 : ℕ) else 0) * (if x ∈ S j then 1 else 0) := by
      exact Finset.sum_comm
    simp_rw [hinter]
    rw [step1, step2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul_sum]
    simp only [← hf x]
    rw [sq]
  have hsum : (∑ i, (S i).card) = ∑ x : ι, deg x := sum_card_eq_sum_degree S
  rw [hsum, hident]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := deg)
  rwa [Finset.card_univ] at hcs

/-- **Second-moment (Johnson-type) list-size bound.**  If each of the `card κ` agreement sets
covers at least `a` of the `|ι|` coordinates and every two *distinct* sets share at most `b`
coordinates, then
`card κ · a² ≤ |ι|² + card κ · |ι| · b`.
In list-decoding terms (sets = agreement supports of codewords with a received word, `a` =
agreement radius, `b` = pairwise agreement = `|ι| − dist`), this is the combinatorial Johnson
list-size engine. -/
theorem card_mul_sq_le_of_agreement {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [Nonempty κ] (S : κ → Finset ι) (a b : ℕ)
    (hlo : ∀ i, a ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b) :
    Fintype.card κ * a ^ 2 ≤ (Fintype.card ι) ^ 2 + Fintype.card κ * Fintype.card ι * b := by
  classical
  have hlb : Fintype.card κ * a ≤ ∑ i, (S i).card := by
    rw [show Fintype.card κ * a = ∑ _i : κ, a by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]]
    exact Finset.sum_le_sum (fun i _ => hlo i)
  have hub : (∑ i, ∑ j, (S i ∩ S j).card)
      ≤ Fintype.card κ * Fintype.card ι + Fintype.card κ * (Fintype.card κ * b) := by
    have hterm : ∀ i j, (S i ∩ S j).card ≤ (if i = j then Fintype.card ι else b) := by
      intro i j
      by_cases h : i = j
      · rw [if_pos h]
        have hss : (S i ∩ S j) ⊆ (Finset.univ : Finset ι) := Finset.subset_univ (S i ∩ S j)
        calc (S i ∩ S j).card
            ≤ (Finset.univ : Finset ι).card := Finset.card_le_card hss
          _ = Fintype.card ι := Finset.card_univ
      · simp only [h, if_false]; exact hpair i j h
    have hinner : ∀ i : κ, (∑ j : κ, (if i = j then Fintype.card ι else b))
        ≤ Fintype.card ι + Fintype.card κ * b := by
      intro i
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, smul_eq_mul]
      have h1 : (Finset.univ.filter (fun j => i = j)).card = 1 := by
        rw [Finset.card_eq_one]; exact ⟨i, by ext j; simp [eq_comm]⟩
      have h2 : (Finset.univ.filter (fun j => ¬ i = j)).card ≤ Fintype.card κ := by
        refine le_trans (Finset.card_filter_le _ _) ?_
        rw [Finset.card_univ]
      rw [h1, one_mul]
      exact Nat.add_le_add_left (Nat.mul_le_mul h2 (le_refl b)) _
    refine le_trans (Finset.sum_le_sum (fun i _ =>
      le_trans (Finset.sum_le_sum (fun j _ => hterm i j)) (hinner i))) ?_
    rw [show (∑ _i : κ, (Fintype.card ι + Fintype.card κ * b))
        = Fintype.card κ * Fintype.card ι + Fintype.card κ * (Fintype.card κ * b) by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_add]]
  have hmass := sq_sum_card_le_card_mul_sum_inter S
  have key : (Fintype.card κ * a) ^ 2
      ≤ Fintype.card ι *
          (Fintype.card κ * Fintype.card ι + Fintype.card κ * (Fintype.card κ * b)) :=
    le_trans (Nat.pow_le_pow_left hlb 2) (le_trans hmass (Nat.mul_le_mul le_rfl hub))
  have e1 : (Fintype.card κ * a) ^ 2 = Fintype.card κ * (Fintype.card κ * a ^ 2) := by
    ring
  have e2 : Fintype.card ι *
        (Fintype.card κ * Fintype.card ι + Fintype.card κ * (Fintype.card κ * b))
      = Fintype.card κ * ((Fintype.card ι) ^ 2 + Fintype.card κ * Fintype.card ι * b) := by
    ring
  rw [e1, e2] at key
  have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr inferInstance
  exact Nat.le_of_mul_le_mul_left key hpos

/-- **Subtracted Johnson-list denominator form.**  If each of the `card κ` agreement sets covers
at least `a` coordinates, pairwise intersections of distinct sets have size at most `b`, and the
Johnson denominator is nonnegative (`|ι|·b ≤ a²`), then

`card κ · (a² - |ι|·b) ≤ |ι|²`.

This is the consumer-facing algebraic form of `card_mul_sq_le_of_agreement`; downstream list-size
bounds can divide by the positive denominator when the inequality is strict. -/
theorem card_mul_sub_le_of_agreement {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] [Nonempty κ] (S : κ → Finset ι) (a b : ℕ)
    (hlo : ∀ i, a ≤ (S i).card)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ b)
    (hgap : Fintype.card ι * b ≤ a ^ 2) :
    Fintype.card κ * (a ^ 2 - Fintype.card ι * b) ≤ (Fintype.card ι) ^ 2 := by
  have key := card_mul_sq_le_of_agreement S a b hlo hpair
  have htail :
      Fintype.card κ * Fintype.card ι * b = Fintype.card κ * (Fintype.card ι * b) := by
    ring
  rw [htail] at key
  have hsplit : Fintype.card κ * a ^ 2 =
      Fintype.card κ * (a ^ 2 - Fintype.card ι * b)
        + Fintype.card κ * (Fintype.card ι * b) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hgap]
  rw [hsplit] at key
  exact Nat.le_of_add_le_add_right key

/-- **Joint-pair existence** (GG25 multi-γ extraction).  If the agreement mass is large enough
— precisely `(card κ)²·t·|ι| + |ι|·∑|S i| < (∑|S i|)²` — then some two *distinct* sets share
strictly more than `t` coordinates.  This is the joint pair the repaired ABF26 T4.21
line-decoding argument extracts (issue #140), obtained from the Cauchy–Schwarz mass bound by
averaging off the diagonal. -/
theorem exists_pair_inter_gt {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (S : κ → Finset ι) (t : ℕ)
    (hbig : (Fintype.card κ) ^ 2 * t * Fintype.card ι + Fintype.card ι * (∑ i, (S i).card)
            < (∑ i, (S i).card) ^ 2) :
    ∃ i j, i ≠ j ∧ t < (S i ∩ S j).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hterm : ∀ i j, (S i ∩ S j).card ≤ (if i = j then (S i).card else t) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [Finset.inter_self]
    · simp only [h, if_false]; exact hcon i j h
  have hinner : ∀ i, (∑ j, (if i = j then (S i).card else t))
      ≤ (S i).card + Fintype.card κ * t := by
    intro i
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul]
    have h1 : (Finset.univ.filter (fun j => i = j)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨i, by ext j; simp [eq_comm]⟩
    have h2 : (Finset.univ.filter (fun j => ¬ i = j)).card ≤ Fintype.card κ := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Finset.card_univ]
    rw [h1, one_mul]
    exact add_le_add_right (Nat.mul_le_mul h2 (le_refl t)) _
  have hbound : (∑ i, ∑ j, (S i ∩ S j).card)
      ≤ ∑ i, ((S i).card + Fintype.card κ * t) := by
    apply Finset.sum_le_sum
    intro i _
    exact le_trans (Finset.sum_le_sum (fun j _ => hterm i j)) (hinner i)
  have heq2 : (∑ i, ((S i).card + Fintype.card κ * t))
      = (∑ i, (S i).card) + Fintype.card κ * (Fintype.card κ * t) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [heq2] at hbound
  have hmass := sq_sum_card_le_card_mul_sum_inter S
  have hchain : (∑ i, (S i).card) ^ 2
      ≤ Fintype.card ι * ((∑ i, (S i).card) + Fintype.card κ * (Fintype.card κ * t)) :=
    le_trans hmass (Nat.mul_le_mul le_rfl hbound)
  have heq : Fintype.card ι * ((∑ i, (S i).card) + Fintype.card κ * (Fintype.card κ * t))
      = (Fintype.card κ) ^ 2 * t * Fintype.card ι + Fintype.card ι * (∑ i, (S i).card) := by
    ring
  rw [heq] at hchain
  omega

end ArkLib.Coverage

#print axioms ArkLib.Coverage.card_mul_sq_le_of_agreement
#print axioms ArkLib.Coverage.card_mul_sub_le_of_agreement
