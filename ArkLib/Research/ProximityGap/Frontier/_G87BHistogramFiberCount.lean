/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G87B: the histogram fiber count — `#{u : Fin k → α | histogram u = x} = multinomial x`

The keystone connecting the histogram-level sharp envelope (G86S) to the word-level collision
sector (G84/G88 decoder lane).  G88's coarse tuple envelope loses `(s!)^2` relative to G86S,
which the G87W Stepanov margin (`2^3.68`) cannot repay at depth four (`(4!)^2 = 2^9.17`); the
production depth-four closure therefore genuinely needs the multiplicity-exact correspondence
between ordered words and their histograms.  This file proves it:

* `sum_histogram` — a `k`-tuple's histogram has total mass `k`;
* `multinomial_lower_recurrence` — the multinomial Pascal recurrence
  `m(x) = sum_{a : x a > 0} m(x - δ_a)` (proved in denominator-cleared form);
* `card_histFiber` — **the counting theorem**: for `∑ x = k`,
  `#{u : Fin k → α | histogram u = x} = Nat.multinomial univ x`.

Consequently every histogram-weighted sum over core pairs (G86S `orderedCoreCount`,
`sectorMass`) is *exactly* a count of ordered word pairs, and the sharp envelope transfers
verbatim to the word-level sector.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87BHistogramFiberCount

open Finset
open scoped Nat

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The histogram (value-multiplicity function) of a tuple. -/
def histogram {k : ℕ} (u : Fin k → α) : α → ℕ :=
  fun a => (Finset.univ.filter fun i => u i = a).card

/-- A `k`-tuple's histogram has total mass `k`. -/
theorem sum_histogram {k : ℕ} (u : Fin k → α) :
    ∑ a : α, histogram u a = k := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := u) (s := Finset.univ) (t := Finset.univ) (fun i _ => Finset.mem_univ _)
  unfold histogram
  rw [← h, Finset.card_univ, Fintype.card_fin]

/-- Decrement a histogram at one letter. -/
def decr (x : α → ℕ) (a : α) : α → ℕ :=
  Function.update x a (x a - 1)

theorem sum_decr (x : α → ℕ) {a : α} (ha : 0 < x a) :
    ∑ b : α, decr x a b = (∑ b : α, x b) - 1 := by
  classical
  unfold decr
  rw [Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase]
  have hmem : a ∈ Finset.univ := Finset.mem_univ a
  have hx : ∑ b : α, x b = x a + ∑ b ∈ Finset.univ.erase a, x b :=
    (Finset.add_sum_erase _ _ hmem).symm
  omega

theorem prod_factorial_decr (x : α → ℕ) {a : α} (ha : 0 < x a) :
    ∏ b : α, (x b)! = x a * ∏ b : α, (decr x a b)! := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun b => (x b)!) (Finset.mem_univ a),
      ← Finset.mul_prod_erase Finset.univ (fun b => (decr x a b)!) (Finset.mem_univ a)]
  have herase : ∀ b ∈ Finset.univ.erase a, (decr x a b)! = (x b)! := by
    intro b hb
    unfold decr
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
  rw [Finset.prod_congr rfl herase]
  have hda : decr x a a = x a - 1 := by
    unfold decr
    rw [Function.update_self]
  rw [hda]
  have hfac : (x a)! = x a * (x a - 1)! := by
    obtain ⟨m, hm⟩ : ∃ m, x a = m + 1 := ⟨x a - 1, by omega⟩
    rw [hm]
    simp [Nat.factorial_succ]
  rw [hfac]
  ring

/-- **The multinomial lower recurrence** (Pascal for multinomials):
`m(x) = ∑_{a : x a > 0} m(x - δ_a)` whenever `x` has positive total mass. -/
theorem multinomial_lower_recurrence (x : α → ℕ) (hx : 0 < ∑ b : α, x b) :
    Nat.multinomial Finset.univ x =
      ∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
        Nat.multinomial Finset.univ (decr x a) := by
  classical
  have hprodpos : 0 < ∏ b : α, (x b)! := Finset.prod_pos fun b _ => Nat.factorial_pos _
  refine (Nat.eq_of_mul_eq_mul_right hprodpos ?_).symm
  have key : ∀ a ∈ Finset.univ.filter (fun a => 0 < x a),
      Nat.multinomial Finset.univ (decr x a) * ∏ b : α, (x b)!
        = x a * ((∑ b : α, x b) - 1)! := by
    intro a ha
    have hxa : 0 < x a := (Finset.mem_filter.mp ha).2
    calc
      Nat.multinomial Finset.univ (decr x a) * ∏ b : α, (x b)!
          = Nat.multinomial Finset.univ (decr x a) *
              (x a * ∏ b : α, (decr x a b)!) := by
            rw [← prod_factorial_decr x hxa]
      _ = x a * ((∏ b : α, (decr x a b)!) * Nat.multinomial Finset.univ (decr x a)) := by
            ring
      _ = x a * (∑ b : α, decr x a b)! := by
            rw [Nat.multinomial_spec]
      _ = x a * ((∑ b : α, x b) - 1)! := by
            rw [sum_decr x hxa]
  calc
    (∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
        Nat.multinomial Finset.univ (decr x a)) * ∏ b : α, (x b)!
        = ∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
            Nat.multinomial Finset.univ (decr x a) * ∏ b : α, (x b)! :=
          Finset.sum_mul _ _ _
    _ = ∑ a ∈ Finset.univ.filter (fun a => 0 < x a), x a * ((∑ b : α, x b) - 1)! :=
          Finset.sum_congr rfl key
    _ = (∑ a ∈ Finset.univ.filter (fun a => 0 < x a), x a) * ((∑ b : α, x b) - 1)! :=
          (Finset.sum_mul _ _ _).symm
    _ = (∑ a : α, x a) * ((∑ b : α, x b) - 1)! := by
          congr 1
          exact Finset.sum_filter_of_ne (fun a _ ha => by omega)
    _ = (∑ b : α, x b)! := by
          obtain ⟨m, hm⟩ : ∃ m, ∑ b : α, x b = m + 1 := ⟨(∑ b : α, x b) - 1, by omega⟩
          rw [hm]
          simp [Nat.factorial_succ]
    _ = Nat.multinomial Finset.univ x * ∏ b : α, (x b)! := by
          rw [mul_comm]
          exact (Nat.multinomial_spec _ _).symm

/-- The fiber of tuples with a given histogram. -/
def histFiber (k : ℕ) (x : α → ℕ) : Finset (Fin k → α) :=
  Finset.univ.filter fun u => histogram u = x

/-- Splitting a histogram at position zero. -/
theorem histogram_succ {k : ℕ} (u : Fin (k + 1) → α) (b : α) :
    histogram u b = histogram (u ∘ Fin.succ) b + (if u 0 = b then 1 else 0) := by
  classical
  unfold histogram
  have : (Finset.univ : Finset (Fin (k + 1))).filter (fun i => u i = b) =
      ((Finset.univ : Finset (Fin k)).filter (fun j => u j.succ = b)).map
        ⟨Fin.succ, Fin.succ_injective k⟩ ∪
        (if u 0 = b then {0} else ∅) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hi
      rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
      · subst h0
        right
        simp [hi]
      · left
        exact ⟨j, by simpa using hi, rfl⟩
    · intro hi
      rcases hi with ⟨j, hj, rfl⟩ | hi
      · simpa using hj
      · split_ifs at hi with hb
        · simp only [Finset.mem_singleton] at hi
          subst hi
          exact hb
        · simp at hi
  rw [this, Finset.card_union_of_disjoint, Finset.card_map]
  · congr 1
    split_ifs <;> simp
  · split_ifs
    · simp only [Finset.disjoint_singleton_right, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      rintro ⟨j, _, hj⟩
      exact (Fin.succ_ne_zero j) hj
    · simp

/-- **The histogram fiber count**: ordered `k`-tuples realizing a histogram `x` of total
mass `k` number exactly `multinomial x`. -/
theorem card_histFiber (k : ℕ) (x : α → ℕ) (hx : ∑ b : α, x b = k) :
    (histFiber k x).card = Nat.multinomial Finset.univ x := by
  classical
  induction k generalizing x with
  | zero =>
      have hx0 : ∀ b, x b = 0 := fun b => (Finset.sum_eq_zero_iff.mp hx) b (Finset.mem_univ b)
      have hmem : ∀ u : Fin 0 → α, u ∈ histFiber 0 x := by
        intro u
        simp only [histFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        funext b
        rw [hx0 b]
        unfold histogram
        simp
      rw [Finset.eq_univ_of_forall hmem, Finset.card_univ]
      have h1 : Fintype.card (Fin 0 → α) = 1 := by simp
      rw [h1]
      have hm1 : Nat.multinomial Finset.univ x = 1 := by
        rw [Nat.multinomial_congr (fun a _ => hx0 a)]
        unfold Nat.multinomial
        simp
      rw [hm1]
  | succ k ih =>
      have hsplit := Finset.card_eq_sum_card_fiberwise
        (f := fun u : Fin (k + 1) → α => u 0) (s := histFiber (k + 1) x)
        (t := Finset.univ) (fun u _ => Finset.mem_univ _)
      rw [hsplit]
      have hfiber : ∀ a : α,
          ((histFiber (k + 1) x).filter fun u => u 0 = a).card =
            if 0 < x a then Nat.multinomial Finset.univ (decr x a) else 0 := by
        intro a
        by_cases hxa : 0 < x a
        · rw [if_pos hxa]
          rw [← ih (decr x a) (by rw [sum_decr x hxa]; omega)]
          apply Finset.card_bij' (fun u _ => u ∘ Fin.succ) (fun v _ => Fin.cons a v)
          · intro u hu
            simp only [Finset.mem_filter, histFiber, Finset.mem_univ, true_and] at hu ⊢
            obtain ⟨hhist, h0⟩ := hu
            funext b
            have hsucc := histogram_succ u b
            rw [hhist] at hsucc
            unfold decr
            by_cases hab : b = a
            · subst hab
              rw [Function.update_self]
              rw [h0] at hsucc
              simp at hsucc
              omega
            · rw [Function.update_of_ne hab]
              rw [h0] at hsucc
              simp [hab, Ne.symm hab] at hsucc
              · omega
          · intro v hv
            simp only [Finset.mem_filter, histFiber, Finset.mem_univ, true_and] at hv ⊢
            constructor
            · funext b
              have hsucc := histogram_succ (Fin.cons a v : Fin (k + 1) → α) b
              have htail : (Fin.cons a v : Fin (k + 1) → α) ∘ Fin.succ = v := by
                funext j
                simp [Fin.cons_succ]
              rw [htail, hv] at hsucc
              rw [hsucc]
              unfold decr
              by_cases hab : b = a
              · subst hab
                rw [Function.update_self]
                simp [Fin.cons_zero]
                omega
              · rw [Function.update_of_ne hab]
                simp [Fin.cons_zero, Ne.symm hab]
            · simp [Fin.cons_zero]
          · intro u hu
            simp only [Finset.mem_filter, histFiber, Finset.mem_univ, true_and] at hu
            funext i
            rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
            · subst h0
              simp [Fin.cons_zero, hu.2]
            · simp [Fin.cons_succ]
          · intro v _
            funext j
            simp [Fin.cons_succ]
        · rw [if_neg hxa]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro u hu
          simp only [Finset.mem_filter, histFiber, Finset.mem_univ, true_and] at hu
          intro h0
          have : 0 < histogram u a := by
            unfold histogram
            rw [Finset.card_pos]
            exact ⟨0, by simp [h0]⟩
          rw [hu] at this
          omega
      calc
        ∑ a : α, ((histFiber (k + 1) x).filter fun u => u 0 = a).card
            = ∑ a : α, if 0 < x a then Nat.multinomial Finset.univ (decr x a) else 0 :=
          Finset.sum_congr rfl fun a _ => hfiber a
        _ = ∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
              Nat.multinomial Finset.univ (decr x a) := by
          rw [Finset.sum_filter]
        _ = Nat.multinomial Finset.univ x :=
          (multinomial_lower_recurrence x (by omega)).symm

end ArkLib.ProximityGap.Frontier.G87BHistogramFiberCount

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G87BHistogramFiberCount.sum_histogram
#print axioms
  ArkLib.ProximityGap.Frontier.G87BHistogramFiberCount.multinomial_lower_recurrence
#print axioms
  ArkLib.ProximityGap.Frontier.G87BHistogramFiberCount.card_histFiber
