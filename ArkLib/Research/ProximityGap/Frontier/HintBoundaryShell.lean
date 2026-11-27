/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank

/-!
# Sharpened Non-Asymptotic Hint Boundary-Shell Theorem for Interleaved RS Lists

We give a completely elementary, division-free integer Cauchy–Schwarz proof of the
sharpened finite-length single-hint Johnson bound (inspired by Kopparty–Sha,
`arXiv:2610.38022`, sharpened with the exact diagonal numerator `(t - d) * H * (n - H)`
rather than `(n - d) * H * (n - H)`).

Specifically, for any field `F`, any injective domain `D : I ↪ F` of length `n`, any
interleaving width `arity`, and any received word `y`:
- If a closed ball of agreement `≥ t` around `y` contains even ONE codeword `h` with
  agreement `≥ H` (where `n * (k - 1) ≤ H * t` and `H * (t - d)² > d * (n - H) * (H - d)`),
  then the ENTIRE ball has cardinality at most
  `1 + ⌊(t - d) * H * (n - H) / (H * (t - d)² - d * (n - H) * (H - d))⌋` (`d = k - 1`).
- Equivalently, EVERY codeword in any over-budget closed ball (`|T| > B`) at `e > nJ`
  is strictly confined to the thin boundary shell `[t, H - 1]`.

At production length `n = 2³⁰`, this confines every over-budget ball (`B₁ = 2³⁰`,
`B₂ = 2³¹`) at the first step beyond Johnson to a remarkably thin shell above `A_J`:
- Rate `1/2` (`J+1`): no codeword with agreement `≥ A_J + 16,510` (`B₁`) / `+15,050` (`B₂`).
- Rate `1/4` (`J+1`): no codeword with agreement `≥ A_J + 36,637` (`B₁`) / `+34,757` (`B₂`).
- Rate `1/8` (`J+1`, `B₁`): no codeword with agreement `≥ A_J + 23,741`;
  Rate `1/8` (`J+2`, `B₂`): no codeword with agreement `≥ A_J + 41,565`.
- Rate `1/16` (`J+1`): no codeword with agreement `≥ A_J + 47,064` (`B₁`) / `+43,737` (`B₂`).
-/

set_option autoImplicit false

namespace ProximityGap.HintBoundaryShell

open Finset Code InterleavedListJohnsonRank
open scoped BigOperators

section CombinatorialHintBound

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem sq_sum_le_card_mul_sum_sq {α : Type*} (U : Finset α) (f : α → ℤ) :
    (∑ x ∈ U, f x) ^ 2 ≤ (U.card : ℤ) * ∑ x ∈ U, f x ^ 2 := by
  let S : ℤ := ∑ x ∈ U, f x
  have hnn : 0 ≤ ∑ x ∈ U, ((U.card : ℤ) * f x - S) ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hexp : ∑ x ∈ U, ((U.card : ℤ) * f x - S) ^ 2 =
      (U.card : ℤ) * ((U.card : ℤ) * (∑ x ∈ U, f x ^ 2) - S ^ 2) := by
    have hterm (x : α) : ((U.card : ℤ) * f x - S) ^ 2 =
        (U.card : ℤ) ^ 2 * f x ^ 2 - 2 * (U.card : ℤ) * S * f x + S ^ 2 := by ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    change (U.card : ℤ) ^ 2 * (∑ x ∈ U, f x ^ 2) - 2 * (U.card : ℤ) * S * S +
      (U.card : ℤ) * S ^ 2 = _
    ring
  rw [hexp] at hnn
  rcases Nat.eq_zero_or_pos U.card with h0 | hpos
  · have hU : U = ∅ := card_eq_zero.mp h0
    simp [hU]
  · have hposZ : (0 : ℤ) < U.card := by exact_mod_cast hpos
    have : 0 ≤ (U.card : ℤ) * (∑ x ∈ U, f x ^ 2) - S ^ 2 :=
      nonneg_of_mul_nonneg_right hnn hposZ
    linarith

/-- Sharpened non-asymptotic single-hint block bound (pure integer arithmetic, zero divisions).
If `S : Fin m → Finset I` are `m` sets of size `t`, pairwise intersecting in `≤ d` points,
and each intersecting a fixed hint set `H_set` of size `H` in `≤ d` points, with
`n * d ≤ H * t`, then:
`m * (H * (t - d)² - d * (n - H) * (H - d)) ≤ (t - d) * H * (n - H)`. -/
theorem block_bound_with_hint {m t d H : ℕ} (H_set : Finset I) (S : Fin m → Finset I)
    (hH : H_set.card = H) (hHle : H ≤ Fintype.card I) (hdt : d ≤ t)
    (hw : ∀ i, (S i).card = t)
    (hpair : Pairwise fun i j => (S i ∩ S j).card ≤ d)
    (hhint : ∀ i, (S i ∩ H_set).card ≤ d)
    (hHt : Fintype.card I * d ≤ H * t) :
    let n : ℤ := Fintype.card I
    (m : ℤ) * ((H : ℤ) * ((t : ℤ) - d) ^ 2 - (d : ℤ) * (n - H) * ((H : ℤ) - d)) ≤
      ((t : ℤ) - d) * (H : ℤ) * (n - H) := by
  dsimp only
  let n : ℤ := Fintype.card I
  have hnH : (0 : ℤ) ≤ n - H := by dsimp [n]; omega
  have htd : (0 : ℤ) ≤ (t : ℤ) - d := by omega
  by_cases hm : m = 0
  · subst hm
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (mul_nonneg htd (Nat.cast_nonneg H)) hnH
  · let deg (x : I) : ℤ := ∑ i : Fin m, if x ∈ S i then 1 else 0
    let A : ℤ := ∑ x ∈ H_set, deg x
    let B : ℤ := ∑ x ∈ H_setᶜ, deg x
    have hsum_all : ∑ x : I, deg x = (m : ℤ) * t := by
      unfold deg
      rw [Finset.sum_comm]
      simp [hw]
    have hAB : A + B = (m : ℤ) * t := by
      dsimp [A, B]
      rw [Finset.sum_add_sum_compl, hsum_all]
    have hAle : A ≤ (m : ℤ) * d := by
      have hAeq : A = ∑ i : Fin m, ((S i ∩ H_set).card : ℤ) := by
        dsimp [A, deg]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter]
        have hfilt : H_set.filter (· ∈ S i) = S i ∩ H_set := by
          ext x; simp [and_comm]
        simp [hfilt]
      rw [hAeq]
      calc
        ∑ i : Fin m, ((S i ∩ H_set).card : ℤ)
          ≤ ∑ _i : Fin m, (d : ℤ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hhint i
        _ = (m : ℤ) * d := by simp
    have hsq_all : ∑ x : I, deg x ^ 2 = ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℤ) := by
      simp_rw [deg, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hterm (x : I) :
          (if x ∈ S i then (1 : ℤ) else 0) * (if x ∈ S j then 1 else 0) =
            if x ∈ S i ∩ S j then 1 else 0 := by
        by_cases hi : x ∈ S i <;> by_cases hj : x ∈ S j <;> simp [hi, hj]
      simp_rw [hterm]
      simp [Finset.sum_boole]
      have : (Finset.univ.filter fun x => x ∈ S i ∧ x ∈ S j) = S i ∩ S j := by
        ext x; simp
      rw [this]
    have hsq_le : ∑ x : I, deg x ^ 2 ≤ (m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d := by
      rw [hsq_all]
      have hrow (i : Fin m) :
          ∑ j : Fin m, ((S i ∩ S j).card : ℤ) ≤ (t : ℤ) + ((m : ℤ) - 1) * d := by
        rw [← Finset.add_sum_erase univ _ (mem_univ i), inter_self, hw i]
        have hoff : ∑ j ∈ univ.erase i, ((S i ∩ S j).card : ℤ) ≤ ((m : ℤ) - 1) * d := by
          calc
            ∑ j ∈ univ.erase i, ((S i ∩ S j).card : ℤ)
              ≤ ∑ _j ∈ univ.erase i, (d : ℤ) :=
                Finset.sum_le_sum fun j hj => by
                  exact_mod_cast hpair (mem_erase.mp hj).1.symm
            _ = (((univ.erase i).card : ℕ) : ℤ) * d := by simp
            _ = ((m : ℤ) - 1) * d := by
                rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin,
                  Nat.cast_sub (Nat.pos_of_ne_zero hm)]
                simp
        linarith
      calc
        ∑ i : Fin m, ∑ j : Fin m, ((S i ∩ S j).card : ℤ)
          ≤ ∑ _i : Fin m, ((t : ℤ) + ((m : ℤ) - 1) * d) := Finset.sum_le_sum fun i _ => hrow i
        _ = (m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d := by simp; ring
    have hcs1 : A ^ 2 ≤ (H : ℤ) * ∑ x ∈ H_set, deg x ^ 2 := by
      simpa [hH] using sq_sum_le_card_mul_sum_sq H_set deg
    have hHccard : ((H_setᶜ).card : ℤ) = n - H := by
      rw [Finset.card_compl, hH, Nat.cast_sub hHle]
    have hcs2 : B ^ 2 ≤ (n - H) * ∑ x ∈ H_setᶜ, deg x ^ 2 := by
      simpa [hHccard] using sq_sum_le_card_mul_sum_sq H_setᶜ deg
    have hcomb : (n - H) * A ^ 2 + (H : ℤ) * B ^ 2 ≤
        (H : ℤ) * (n - H) * ((m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d) := by
      have h1 : (n - H) * A ^ 2 ≤ (n - H) * ((H : ℤ) * ∑ x ∈ H_set, deg x ^ 2) :=
        mul_le_mul_of_nonneg_left hcs1 hnH
      have h2 : (H : ℤ) * B ^ 2 ≤ (H : ℤ) * ((n - H) * ∑ x ∈ H_setᶜ, deg x ^ 2) :=
        mul_le_mul_of_nonneg_left hcs2 (Nat.cast_nonneg H)
      have hsum_sq : (∑ x ∈ H_set, deg x ^ 2) + (∑ x ∈ H_setᶜ, deg x ^ 2) = ∑ x : I, deg x ^ 2 :=
        Finset.sum_add_sum_compl H_set (fun x => deg x ^ 2)
      have h3 : (H : ℤ) * (n - H) * (∑ x : I, deg x ^ 2) ≤
          (H : ℤ) * (n - H) * ((m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d) :=
        mul_le_mul_of_nonneg_left hsq_le (mul_nonneg (Nat.cast_nonneg H) hnH)
      calc
        (n - H) * A ^ 2 + (H : ℤ) * B ^ 2
          ≤ (n - H) * ((H : ℤ) * ∑ x ∈ H_set, deg x ^ 2) +
              (H : ℤ) * ((n - H) * ∑ x ∈ H_setᶜ, deg x ^ 2) := add_le_add h1 h2
        _ = (H : ℤ) * (n - H) * ((∑ x ∈ H_set, deg x ^ 2) + (∑ x ∈ H_setᶜ, deg x ^ 2)) := by ring
        _ = (H : ℤ) * (n - H) * (∑ x : I, deg x ^ 2) := by rw [hsum_sq]
        _ ≤ (H : ℤ) * (n - H) * ((m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d) := h3
    -- Exact algebraic convexity identity: since `A ≤ m * d` and `n * d ≤ H * t`,
    -- `(n - H) * A² + H * (m*t - A)² ≥ m² * ((n - H) * d² + H * (t - d)²)`.
    have hB_eq : B = (m : ℤ) * t - A := by linarith
    have hHtZ : n * d ≤ (H : ℤ) * t := by dsimp [n]; exact_mod_cast hHt
    have hdiff :
        ((n - H) * A ^ 2 + (H : ℤ) * B ^ 2) -
          (m : ℤ) ^ 2 * ((n - H) * (d : ℤ) ^ 2 + (H : ℤ) * ((t : ℤ) - d) ^ 2) =
        ((m : ℤ) * d - A) * (2 * (m : ℤ) * ((H : ℤ) * t - n * d) + n * ((m : ℤ) * d - A)) := by
      rw [hB_eq]; ring
    have hdiff_nn : 0 ≤ ((n - H) * A ^ 2 + (H : ℤ) * B ^ 2) -
        (m : ℤ) ^ 2 * ((n - H) * (d : ℤ) ^ 2 + (H : ℤ) * ((t : ℤ) - d) ^ 2) := by
      rw [hdiff]
      have h1 : 0 ≤ (m : ℤ) * d - A := by linarith
      have h2 : 0 ≤ 2 * (m : ℤ) * ((H : ℤ) * t - n * d) :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (by linarith)
      have h3 : 0 ≤ n * ((m : ℤ) * d - A) := mul_nonneg (Nat.cast_nonneg _) h1
      exact mul_nonneg h1 (add_nonneg h2 h3)
    have hmain : (m : ℤ) ^ 2 * ((n - H) * (d : ℤ) ^ 2 + (H : ℤ) * ((t : ℤ) - d) ^ 2) ≤
        (H : ℤ) * (n - H) * ((m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d) := by
      linarith
    have hfactor :
        (m : ℤ) * (((t : ℤ) - d) * (H : ℤ) * (n - H) -
          (m : ℤ) * ((H : ℤ) * ((t : ℤ) - d) ^ 2 - (d : ℤ) * (n - H) * ((H : ℤ) - d))) =
        (H : ℤ) * (n - H) * ((m : ℤ) * t + (m : ℤ) * ((m : ℤ) - 1) * d) -
          (m : ℤ) ^ 2 * ((n - H) * (d : ℤ) ^ 2 + (H : ℤ) * ((t : ℤ) - d) ^ 2) := by
      ring
    have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hfinal : 0 ≤ ((t : ℤ) - d) * (H : ℤ) * (n - H) -
        (m : ℤ) * ((H : ℤ) * ((t : ℤ) - d) ^ 2 - (d : ℤ) * (n - H) * ((H : ℤ) - d)) := by
      apply nonneg_of_mul_nonneg_right _ hmpos
      rw [hfactor]
      linarith
    linarith

end CombinatorialHintBound

section ReedSolomonShell

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Exact single-hint list cap for interleaved Reed–Solomon codes over arbitrary fields,
arbitrary injective domains, and arbitrary widths: if a finite collection `T` of codewords
each agreeing with `y` in `≥ t` sites contains at least one codeword `h` agreeing with `y`
in `≥ H` sites, then `T.card ≤ B`. -/
theorem ball_card_le_of_hint {F : Type*} [Field F] [DecidableEq F] [Nonempty I] (D : I ↪ F)
    (k t H arity B : ℕ) (hHle : H ≤ Fintype.card I) (hdt : k - 1 ≤ t)
    (hHt : Fintype.card I * (k - 1) ≤ H * t)
    (hden : (0 : ℤ) < (H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
      ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ)))
    (hbudget : ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) * (H : ℤ) * ((Fintype.card I : ℤ) - H) <
      (B : ℤ) * ((H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
        ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ))))
    (y : I → Fin arity → F) (T : Finset (I → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F)))
    (hagree : ∀ w ∈ T, t ≤ agree w y)
    (hhint : ∃ h ∈ T, H ≤ agree h y) :
    T.card ≤ B := by
  classical
  rcases hhint with ⟨h, hhT, hhH⟩
  let supp (w : I → Fin arity → F) : Finset I := univ.filter fun x => w x = y x
  have hsupp_card (w : I → Fin arity → F) : (supp w).card = agree w y := by
    simp [supp, Code.agree]
  obtain ⟨H_set, hHsub, hHcard⟩ := Finset.exists_subset_card_eq (hsupp_card h ▸ hhH)
  let T' := T.erase h
  let e := (Fintype.equivFin ↥T').symm
  let word (i : Fin (Fintype.card ↥T')) := (e i).val
  have hword_mem (i) : word i ∈ T := mem_of_mem_erase (e i).property
  have hword_ne (i) : word i ≠ h := (mem_erase.mp (e i).property).1
  choose S hSsub hScard using fun i =>
    Finset.exists_subset_card_eq (hsupp_card (word i) ▸ hagree (word i) (hword_mem i))
  have hpair : Pairwise fun i j => (S i ∩ S j).card ≤ k - 1 := by
    intro i j hij
    have hne : word i ≠ word j := fun he => hij (e.injective (Subtype.ext he))
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode (word j) (hword_mem j)) hne
    have hle : (S i ∩ S j).card ≤ agree (word i) (word j) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
      have hi := (Finset.mem_filter.mp (hSsub i hxi)).2
      have hj := (Finset.mem_filter.mp (hSsub j hxj)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hi.trans hj.symm⟩
    omega
  have hhint_cap (i) : (S i ∩ H_set).card ≤ k - 1 := by
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hcode (word i) (hword_mem i)) (hcode h hhT) (hword_ne i)
    have hle : (S i ∩ H_set).card ≤ agree (word i) h := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxh⟩ := Finset.mem_inter.mp hx
      have hi := (Finset.mem_filter.mp (hSsub i hxi)).2
      have hh' := (Finset.mem_filter.mp (hHsub hxh)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hi.trans hh'.symm⟩
    omega
  have hblk := block_bound_with_hint H_set S hHcard hHle hdt hScard hpair hhint_cap hHt
  have hT'card : Fintype.card ↥T' = T.card - 1 := by
    rw [Fintype.card_coe, card_erase_of_mem hhT]
  by_contra! hgt
  have hgeB : (B : ℤ) ≤ (Fintype.card ↥T' : ℤ) := by
    rw [hT'card]
    have : B ≤ T.card - 1 := by omega
    exact_mod_cast this
  have hmul : (B : ℤ) * ((H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
      ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ))) ≤
      (Fintype.card ↥T' : ℤ) * ((H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
        ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ))) :=
    mul_le_mul_of_nonneg_right hgeB hden.le
  linarith

/-- Contrapositive thin-shell confinement: EVERY codeword in an over-budget ball (`B < T.card`)
of agreement `≥ t` must have agreement strictly `< H`. -/
theorem over_budget_ball_thin_shell {F : Type*} [Field F] [DecidableEq F] [Nonempty I] (D : I ↪ F)
    (k t H arity B : ℕ) (hHle : H ≤ Fintype.card I) (hdt : k - 1 ≤ t)
    (hHt : Fintype.card I * (k - 1) ≤ H * t)
    (hden : (0 : ℤ) < (H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
      ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ)))
    (hbudget : ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) * (H : ℤ) * ((Fintype.card I : ℤ) - H) <
      (B : ℤ) * ((H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
        ((k - 1 : ℕ) : ℤ) * ((Fintype.card I : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ))))
    (y : I → Fin arity → F) (T : Finset (I → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F)))
    (hagree : ∀ w ∈ T, t ≤ agree w y)
    (hover : B < T.card) :
    ∀ w ∈ T, agree w y < H := by
  intro w hw
  by_contra! hge
  have hle := ball_card_le_of_hint D k t H arity B hHle hdt hHt hden hbudget y T hcode hagree ⟨w, hw, hge⟩
  omega

end ReedSolomonShell

section ProductionShells

private theorem shell_2p30 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F)
    (k t H arity B : ℕ) (hHle : H ≤ 1073741824) (hdt : k - 1 ≤ t)
    (hHt : 1073741824 * (k - 1) ≤ H * t)
    (hden : (0 : ℤ) < (H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
      ((k - 1 : ℕ) : ℤ) * ((1073741824 : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ)))
    (hbudget : ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) * (H : ℤ) * ((1073741824 : ℤ) - H) <
      (B : ℤ) * ((H : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ)) ^ 2 -
        ((k - 1 : ℕ) : ℤ) * ((1073741824 : ℤ) - H) * ((H : ℤ) - ((k - 1 : ℕ) : ℤ))))
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, t ≤ agree w y) (hover : B < T.card) :
    ∀ w ∈ T, agree w y < H :=
  over_budget_ball_thin_shell D k t H arity B (by simpa using hHle) hdt (by simpa using hHt)
    (by simpa using hden) (by simpa using hbudget) y T hcode hagree hover

/-- Rate `1/2`, `J+1` (`t = 759,250,124`): any ball of size `> B₁ = 2³⁰` has EVERY
codeword strictly below agreement `759,266,635` (`A_J + 16,510`). -/
theorem rate_half_j1_shell_B1 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 536870912 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 759250124 ≤ agree w y) (hover : 1073741824 < T.card) :
    ∀ w ∈ T, agree w y < 759266635 :=
  shell_2p30 D 536870912 759250124 759266635 arity 1073741824
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/2`, `J+1` (`t = 759,250,124`): any ball of size `> B₂ = 2³¹` has EVERY
codeword strictly below agreement `759,265,175` (`A_J + 15,050`). -/
theorem rate_half_j1_shell_B2 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 536870912 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 759250124 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 759265175 :=
  shell_2p30 D 536870912 759250124 759265175 arity 2147483648
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/4`, `J+1` (`t = 536,870,910`): any ball of size `> B₁ = 2³⁰` has EVERY
codeword strictly below agreement `536,907,548` (`A_J + 36,637`). -/
theorem rate_quarter_j1_shell_B1 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 268435456 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 536870910 ≤ agree w y) (hover : 1073741824 < T.card) :
    ∀ w ∈ T, agree w y < 536907548 :=
  shell_2p30 D 268435456 536870910 536907548 arity 1073741824
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/4`, `J+1` (`t = 536,870,910`): any ball of size `> B₂ = 2³¹` has EVERY
codeword strictly below agreement `536,905,668` (`A_J + 34,757`). -/
theorem rate_quarter_j1_shell_B2 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 268435456 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 536870910 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 536905668 :=
  shell_2p30 D 268435456 536870910 536905668 arity 2147483648
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/8`, `J+1` (`t = 379,625,061`, the sharpest `p₁` open target): any ball of size
`> B₁ = 2³⁰` has EVERY codeword strictly below agreement `379,648,803` (`A_J + 23,741`). -/
theorem rate_eighth_j1_shell_B1 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 379625061 ≤ agree w y) (hover : 1073741824 < T.card) :
    ∀ w ∈ T, agree w y < 379648803 :=
  shell_2p30 D 134217728 379625061 379648803 arity 1073741824
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/8`, `J+2` (`t = 379,625,060`, the `p₂` open target): any ball of size
`> B₂ = 2³¹` has EVERY codeword strictly below agreement `379,666,627` (`A_J + 41,565`). -/
theorem rate_eighth_j2_shell_B2 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 134217728 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 379625060 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 379666627 :=
  shell_2p30 D 134217728 379625060 379666627 arity 2147483648
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/16`, `J+1` (`t = 268,435,453`): any ball of size `> B₁ = 2³⁰` has EVERY
codeword strictly below agreement `268,482,518` (`A_J + 47,064`). -/
theorem rate_sixteenth_j1_shell_B1 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 67108864 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 268435453 ≤ agree w y) (hover : 1073741824 < T.card) :
    ∀ w ∈ T, agree w y < 268482518 :=
  shell_2p30 D 67108864 268435453 268482518 arity 1073741824
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

/-- Rate `1/16`, `J+1` (`t = 268,435,453`): any ball of size `> B₂ = 2³¹` has EVERY
codeword strictly below agreement `268,479,191` (`A_J + 43,737`). -/
theorem rate_sixteenth_j1_shell_B2 {F : Type*} [Field F] [DecidableEq F] (D : Fin 1073741824 ↪ F) (arity : ℕ)
    (y : Fin 1073741824 → Fin arity → F) (T : Finset (Fin 1073741824 → Fin arity → F))
    (hcode : ∀ w ∈ T, w ∈ interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 67108864 : Set (Fin 1073741824 → F)))
    (hagree : ∀ w ∈ T, 268435453 ≤ agree w y) (hover : 2147483648 < T.card) :
    ∀ w ∈ T, agree w y < 268479191 :=
  shell_2p30 D 67108864 268435453 268479191 arity 2147483648
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y T hcode hagree hover

end ProductionShells

end ProximityGap.HintBoundaryShell

#print axioms ProximityGap.HintBoundaryShell.block_bound_with_hint
#print axioms ProximityGap.HintBoundaryShell.ball_card_le_of_hint
#print axioms ProximityGap.HintBoundaryShell.over_budget_ball_thin_shell
#print axioms ProximityGap.HintBoundaryShell.rate_half_j1_shell_B1
#print axioms ProximityGap.HintBoundaryShell.rate_half_j1_shell_B2
#print axioms ProximityGap.HintBoundaryShell.rate_quarter_j1_shell_B1
#print axioms ProximityGap.HintBoundaryShell.rate_quarter_j1_shell_B2
#print axioms ProximityGap.HintBoundaryShell.rate_eighth_j1_shell_B1
#print axioms ProximityGap.HintBoundaryShell.rate_eighth_j2_shell_B2
#print axioms ProximityGap.HintBoundaryShell.rate_sixteenth_j1_shell_B1
#print axioms ProximityGap.HintBoundaryShell.rate_sixteenth_j1_shell_B2
