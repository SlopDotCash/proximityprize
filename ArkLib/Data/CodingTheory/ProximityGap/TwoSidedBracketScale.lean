/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# Round 18 (Issue #232) — the PRIZE-SCALE TWO-SIDED BRACKET in one self-contained file

Composes the two sides into explicit statements at genuine prize scale (`n = 2^20`, rate `1/2`,
`q ≤ 2^256`, prize threshold `Lstar = 2^128 ≥ ε*·|F|`):

* **Johnson side** (`johnson_list_cap`, the classical second-moment list cap re-proved via the
  truncated double count): a family of `L` codewords, each agreeing with a received word on a
  chosen `a`-subset of `n` points, pairwise jointly agreeing on `≤ J` points (`J = k−1` for
  distinct degree-`<k` polynomials), satisfies — over `ℤ` —

    `L · (a² − n·J) ≤ n · a`.

  At `n = 2^20`, `k = 2^19`, `J = k−1`, `a = 750000` (relative radius `δ ≈ 0.2848`, just below
  Johnson `1−√ρ ≈ 0.2929`): the cap gives `L ≤ 61` (`johnson_side_instance`) — microscopic against
  the prize threshold `2^128`.

* **Capacity side** (`capacity_crossover`, the round-14 crossover): at `a = 2^19 + 4063`
  (`δ ≈ 0.49613`), `2^128 · q^4063 < C(2^20, 2^19 + 4063)` for every `q ≤ 2^256` — composed with
  the averaging pigeonhole the list at that radius EXCEEDS the prize threshold.

* **`two_sided_bracket_n2_20`** packages both: for `RS[F, 2^20, 2^19]`-shaped families, the
  prize-threshold agreement `a*` is trapped: lists are `≤ 61 ≪ 2^128` at `a = 750000` and
  `> 2^128` (given the pigeonhole) at `a = 528351` — i.e. **`δ* ∈ [0.2848, 0.49613)`**.

The Johnson-side argument (exact, no `Real.sqrt`): let `m x := #{c : x ∈ A c}`. Then
`∑_x m x = L·a` (double count), `∑_x (m x)² = ∑_{(c,c')} |A c ∩ A c'| ≤ L·a + L²·J` (diagonal +
off-diagonal), and Cauchy–Schwarz `(∑ m)² ≤ n · ∑ m²` assemble into the cap.
-/

open Finset

namespace Round18Bracket

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The fiber count `m x = #{c : x ∈ A c}`. -/
def fiberCount (A : κ → Finset ι) (x : ι) : ℕ :=
  (Finset.univ.filter (fun c : κ => x ∈ A c)).card

/-- Indicator sum over the whole domain counts membership. -/
theorem sum_indicator_mem (s : Finset ι) :
    (∑ x : ι, if x ∈ s then (1 : ℕ) else 0) = s.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

omit [DecidableEq κ] in
/-- **Double count (first moment):** `∑_x m x = ∑_c |A c|`. -/
theorem sum_fiberCount (A : κ → Finset ι) :
    ∑ x : ι, fiberCount A x = ∑ c : κ, (A c).card := by
  classical
  unfold fiberCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact sum_indicator_mem (A c)

omit [DecidableEq κ] in
/-- **Second moment as a pair sum:** `∑_x (m x)² = ∑_{(c,c') : κ×κ} |A c ∩ A c'|`. -/
theorem sum_fiberCount_sq (A : κ → Finset ι) :
    ∑ x : ι, (fiberCount A x) ^ 2 = ∑ p : κ × κ, (A p.1 ∩ A p.2).card := by
  classical
  unfold fiberCount
  have hsq : ∀ x : ι, ((Finset.univ.filter (fun c : κ => x ∈ A c)).card) ^ 2
      = ∑ p : κ × κ, (if x ∈ A p.1 ∩ A p.2 then 1 else 0) := by
    intro x
    rw [sq, Finset.card_filter, Finset.sum_mul_sum, ← Finset.sum_product',
        Finset.univ_product_univ]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h1 : x ∈ A p.1 <;> by_cases h2 : x ∈ A p.2 <;>
      simp [h1, h2, Finset.mem_inter]
  rw [Finset.sum_congr rfl (fun x _ => hsq x), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact sum_indicator_mem (A p.1 ∩ A p.2)

omit [Fintype ι] in
/-- **Pair-sum bound:** diagonal contributes `∑_c |A c|`, each off-diagonal term is `≤ J`. -/
theorem pair_sum_le (A : κ → Finset ι) (a J : ℕ) (hA : ∀ c, (A c).card = a)
    (hpair : ∀ c c' : κ, c ≠ c' → (A c ∩ A c').card ≤ J) :
    ∑ p : κ × κ, (A p.1 ∩ A p.2).card
      ≤ Fintype.card κ * a + Fintype.card κ * Fintype.card κ * J := by
  classical
  have hterm : ∀ p : κ × κ, (A p.1 ∩ A p.2).card
      ≤ (if p.1 = p.2 then a else J) := by
    intro p
    by_cases h : p.1 = p.2
    · rw [if_pos h, h, Finset.inter_self]
      exact le_of_eq (hA p.2)
    · rw [if_neg h]
      exact hpair p.1 p.2 h
  calc ∑ p : κ × κ, (A p.1 ∩ A p.2).card
      ≤ ∑ p : κ × κ, (if p.1 = p.2 then a else J) := Finset.sum_le_sum (fun p _ => hterm p)
    _ ≤ ∑ p : κ × κ, ((if p.1 = p.2 then a else 0) + J) := by
        apply Finset.sum_le_sum
        intro p _
        by_cases h : p.1 = p.2 <;> simp [h]
    _ = (∑ p : κ × κ, (if p.1 = p.2 then a else 0)) + Fintype.card κ * Fintype.card κ * J := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            smul_eq_mul]
    _ ≤ Fintype.card κ * a + Fintype.card κ * Fintype.card κ * J := by
        apply Nat.add_le_add_right
        -- the diagonal indicator sum is (#diagonal)·a ≤ L·a
        have hdiag : ∑ p : κ × κ, (if p.1 = p.2 then a else 0)
            = ((Finset.univ : Finset (κ × κ)).filter (fun p => p.1 = p.2)).card * a := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        rw [hdiag]
        apply Nat.mul_le_mul_right
        -- the diagonal injects into κ
        have hinj := Finset.card_le_card_of_injOn (fun p : κ × κ => p.1)
          (s := (Finset.univ : Finset (κ × κ)).filter (fun p => p.1 = p.2))
          (t := (Finset.univ : Finset κ))
          (fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _))
          (fun p hp p' hp' h => by
            simp only [Finset.mem_coe, Finset.mem_filter] at hp hp'
            exact Prod.ext h (by rw [← hp.2, ← hp'.2]; exact h))
        rwa [Finset.card_univ] at hinj

/-- **The Johnson-side list cap (classical second-moment bound, exact integer form).** A family
`A : κ → Finset ι` of `a`-subsets of an `n`-point domain with pairwise intersections `≤ J`
satisfies `L·(a² − n·J) ≤ n·a` over `ℤ` (`L = |κ|`). For `a² > n·J` (below the Johnson radius)
this caps `L ≤ n·a/(a² − n·J)`. -/
theorem johnson_list_cap (A : κ → Finset ι) (a J : ℕ) (hA : ∀ c, (A c).card = a)
    (hpair : ∀ c c' : κ, c ≠ c' → (A c ∩ A c').card ≤ J) :
    (Fintype.card κ : ℤ) * ((a : ℤ) ^ 2 - (Fintype.card ι : ℤ) * J)
      ≤ (Fintype.card ι : ℤ) * a := by
  classical
  have hcs : (∑ x : ι, fiberCount A x) ^ 2
      ≤ Fintype.card ι * ∑ x : ι, (fiberCount A x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun x => fiberCount A x)
    rwa [Finset.card_univ] at h
  have h1 : ∑ x : ι, fiberCount A x = Fintype.card κ * a := by
    rw [sum_fiberCount, Finset.sum_congr rfl (fun c _ => hA c), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
  have h2 : ∑ x : ι, (fiberCount A x) ^ 2
      ≤ Fintype.card κ * a + Fintype.card κ * Fintype.card κ * J := by
    rw [sum_fiberCount_sq]
    exact pair_sum_le A a J hA hpair
  have hmain : (Fintype.card κ * a) ^ 2
      ≤ Fintype.card ι * (Fintype.card κ * a + Fintype.card κ * Fintype.card κ * J) := by
    calc (Fintype.card κ * a) ^ 2 = (∑ x : ι, fiberCount A x) ^ 2 := by rw [h1]
      _ ≤ Fintype.card ι * ∑ x : ι, (fiberCount A x) ^ 2 := hcs
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  rcases Nat.eq_zero_or_pos (Fintype.card κ) with hL0 | hLpos
  · rw [hL0]
    push_cast
    have hnn : (0 : ℤ) ≤ (Fintype.card ι : ℤ) * a := by positivity
    linarith
  · have hdiv : Fintype.card κ * (a * a)
        ≤ Fintype.card ι * a + Fintype.card ι * Fintype.card κ * J := by
      have hexp : Fintype.card κ * (Fintype.card κ * (a * a))
          ≤ Fintype.card κ * (Fintype.card ι * a + Fintype.card ι * Fintype.card κ * J) := by
        calc Fintype.card κ * (Fintype.card κ * (a * a)) = (Fintype.card κ * a) ^ 2 := by ring
          _ ≤ Fintype.card ι * (Fintype.card κ * a + Fintype.card κ * Fintype.card κ * J) := hmain
          _ = Fintype.card κ * (Fintype.card ι * a + Fintype.card ι * Fintype.card κ * J) := by
              ring
      exact Nat.le_of_mul_le_mul_left hexp hLpos
    push_cast at hdiv ⊢
    nlinarith [hdiv]

/-! ## 2. The Johnson-side prize-scale instance -/

/-- **Johnson side at `n = 2^20`, rate 1/2:** at agreement `a = 750000` (relative radius
`δ ≈ 0.2848`), any family of pairwise-`(k−1)`-intersecting `a`-sets has `L ≤ 61` members —
microscopic against the prize threshold `2^128`. (`a² − n(k−1) = 12 745 234 688 > 0` and
`62 · 12 745 234 688 > 2^20 · 750000`.) -/
theorem johnson_side_instance (A : κ → Finset ι) (hι : Fintype.card ι = 2 ^ 20)
    (hA : ∀ c, (A c).card = 750000)
    (hpair : ∀ c c' : κ, c ≠ c' → (A c ∩ A c').card ≤ 2 ^ 19 - 1) :
    Fintype.card κ ≤ 61 := by
  have h := johnson_list_cap A 750000 (2 ^ 19 - 1) hA hpair
  rw [hι] at h
  by_contra hgt
  push Not at hgt
  have h62 : (62 : ℤ) ≤ (Fintype.card κ : ℤ) := by exact_mod_cast hgt
  -- 62 · (750000² − 2^20·(2^19−1)) > 2^20 · 750000 — pure arithmetic.
  have harith : (2 ^ 20 : ℤ) * 750000 < 62 * ((750000 : ℤ) ^ 2 - 2 ^ 20 * (2 ^ 19 - 1)) := by
    norm_num
  have hpos : (0 : ℤ) ≤ (750000 : ℤ) ^ 2 - 2 ^ 20 * (2 ^ 19 - 1) := by norm_num
  have hmul : (62 : ℤ) * ((750000 : ℤ) ^ 2 - 2 ^ 20 * (2 ^ 19 - 1))
      ≤ (Fintype.card κ : ℤ) * ((750000 : ℤ) ^ 2 - 2 ^ 20 * (2 ^ 19 - 1)) :=
    mul_le_mul_of_nonneg_right h62 hpos
  -- push the ℕ-subtraction form of h to match
  have h' : (Fintype.card κ : ℤ) * ((750000 : ℤ) ^ 2 - 2 ^ 20 * ((2 ^ 19 : ℤ) - 1))
      ≤ (2 ^ 20 : ℤ) * 750000 := by
    have hsub : ((2 ^ 19 - 1 : ℕ) : ℤ) = (2 ^ 19 : ℤ) - 1 := by norm_num
    rw [← hsub]
    exact_mod_cast h
  linarith [h', harith, hmul]

/-! ## 3. The capacity-side crossover (round-14, restated self-contained) -/

/-- Pascal shift `C(n,m) ≤ C(n+j, m+j)`. -/
theorem choose_le_add_add (n m j : ℕ) : n.choose m ≤ (n + j).choose (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc n.choose m ≤ (n + j).choose (m + j) := ih
      _ ≤ (n + j + 1).choose (m + j + 1) := by
          rw [Nat.choose_succ_succ']
          exact Nat.le_add_right _ _

/-- **Capacity-side crossover at prize scale** (= round-14 `crossover_rate_half`): for `t < m`,
`m ≤ 2^62`, `258t + 193 ≤ 2m`, `q ≤ 2^256`, `Lstar ≤ 2^128`: `Lstar·q^t < C(2m, m+t)`. -/
theorem capacity_crossover {m t q Lstar : ℕ}
    (ht : t < m) (hm : m ≤ 2 ^ 62) (hscale : 258 * t + 193 ≤ 2 * m)
    (hq : q ≤ 2 ^ 256) (hL : Lstar ≤ 2 ^ 128) :
    Lstar * q ^ t < (2 * m).choose (m + t) := by
  have hshift : Nat.centralBinom (m - t) ≤ (2 * m).choose (m + t) := by
    have h := choose_le_add_add (2 * (m - t)) (m - t) (2 * t)
    have e1 : 2 * (m - t) + 2 * t = 2 * m := by omega
    have e2 : m - t + 2 * t = m + t := by omega
    rw [e1, e2] at h
    exact h
  have hcb : 4 ^ (m - t) ≤ 2 * (m - t) * Nat.centralBinom (m - t) :=
    Nat.four_pow_le_two_mul_self_mul_centralBinom (m - t) (by omega)
  have h1 : Lstar * q ^ t ≤ 2 ^ (128 + 256 * t) := by
    calc Lstar * q ^ t ≤ 2 ^ 128 * (2 ^ 256) ^ t :=
          Nat.mul_le_mul hL (Nat.pow_le_pow_left hq t)
      _ = 2 ^ (128 + 256 * t) := by rw [← Nat.pow_mul, ← Nat.pow_add]
  have h2 : 2 * (m - t) * 2 ^ (128 + 256 * t) < 4 ^ (m - t) := by
    have hmt : 2 * (m - t) ≤ 2 ^ 63 := by
      calc 2 * (m - t) ≤ 2 * m := by omega
        _ ≤ 2 * 2 ^ 62 := by omega
        _ = 2 ^ 63 := by norm_num
    have hfour : (4 : ℕ) ^ (m - t) = 2 ^ (2 * (m - t)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← Nat.pow_mul]
    rw [hfour]
    calc 2 * (m - t) * 2 ^ (128 + 256 * t)
        ≤ 2 ^ 63 * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_right _ hmt
      _ = 2 ^ (191 + 256 * t) := by rw [← Nat.pow_add]; congr 1; omega
      _ < 2 ^ (2 * (m - t)) := by
          apply Nat.pow_lt_pow_right (by norm_num)
          omega
  have h4 : 2 * (m - t) * (Lstar * q ^ t) < 2 * (m - t) * (2 * m).choose (m + t) := by
    calc 2 * (m - t) * (Lstar * q ^ t)
        ≤ 2 * (m - t) * 2 ^ (128 + 256 * t) := Nat.mul_le_mul_left _ h1
      _ < 4 ^ (m - t) := h2
      _ ≤ 2 * (m - t) * Nat.centralBinom (m - t) := hcb
      _ ≤ 2 * (m - t) * (2 * m).choose (m + t) := Nat.mul_le_mul_left _ hshift
  exact Nat.lt_of_mul_lt_mul_left h4

/-! ## 4. The two-sided prize-scale bracket -/

/-- **THE TWO-SIDED BRACKET at `n = 2^20`, rate 1/2, prize fields.** Both sides in one statement:

* **(Johnson side, `δ ≈ 0.2848`):** any `RS`-shaped family (pairwise joint agreement `≤ k−1`) of
  codewords agreeing with a word on `750000`-subsets has `≤ 61 ≪ 2^128` members.
* **(capacity side, `δ ≈ 0.49613`):** `2^128 · q^4063 < C(2^20, 2^19+4063)` for every prize field
  `q ≤ 2^256` — via the averaging pigeonhole, some word's list at agreement `524288 + 4063`
  exceeds the prize threshold.

Hence the prize-threshold agreement `a*` is trapped in `(528351, 750000]`:
**`δ* ∈ [0.2848, 0.49613)`** for `RS[F, 2^20, 2^19]` at `ε*·|F| ≤ 2^128`. -/
theorem two_sided_bracket_n2_20 :
    (∀ {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type} [Fintype ι] [DecidableEq ι]
        (A : κ → Finset ι), Fintype.card ι = 2 ^ 20 →
        (∀ c, (A c).card = 750000) →
        (∀ c c' : κ, c ≠ c' → (A c ∩ A c').card ≤ 2 ^ 19 - 1) →
        Fintype.card κ ≤ 61) ∧
    (∀ q : ℕ, q ≤ 2 ^ 256 →
        (2 ^ 128 : ℕ) * q ^ 4063 < (2 * 2 ^ 19).choose (2 ^ 19 + 4063)) := by
  constructor
  · intro κ _ _ ι _ _ A hι hA hpair
    exact johnson_side_instance A hι hA hpair
  · intro q hq
    exact capacity_crossover (by norm_num) (by norm_num) (by norm_num) hq (le_refl _)

end Round18Bracket

#print axioms Round18Bracket.sum_fiberCount
#print axioms Round18Bracket.sum_fiberCount_sq
#print axioms Round18Bracket.pair_sum_le
#print axioms Round18Bracket.johnson_list_cap
#print axioms Round18Bracket.johnson_side_instance
#print axioms Round18Bracket.capacity_crossover
#print axioms Round18Bracket.two_sided_bracket_n2_20
